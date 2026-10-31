importScripts("./vendor/vision_bundle.js");

const { FilesetResolver, HandLandmarker } = Vision;

const DETECT_INTERVAL = 1000 / 32;
const MAX_DRAIN = 8;
const GPU_DOWNGRADE_MS = 65;

let landmarker = null;
let initializing = false;
let streamGeneration = 0;
let streamReader = null;
let activeTrack = null;
let pendingFrame = null;
let readPromise = null;
let readResult = null;
let detectMsAverage = 0;
let detectCount = 0;
let delegateUsed = "CPU";
let delegateSettled = false;
let visionInstance = null;
let modelAssetUrl = null;
let landmarkerOptions = null;

function recordDetect(cost) {
  detectMsAverage = detectMsAverage ? detectMsAverage * 0.78 + cost * 0.22 : cost;
  detectCount += 1;
}

function reportStats() {
  self.postMessage({ type: "stats", detectMs: detectMsAverage, delegate: delegateUsed });
}

function buildLandmarker(delegate) {
  return HandLandmarker.createFromOptions(visionInstance, {
    ...landmarkerOptions,
    baseOptions: { modelAssetPath: modelAssetUrl, delegate },
  });
}

async function initialize() {
  if (landmarker) {
    self.postMessage({
      type: "ready",
      supportsTrackProcessor: typeof MediaStreamTrackProcessor !== "undefined",
      delegate: delegateUsed,
    });
    return;
  }
  if (initializing) return;
  initializing = true;

  try {
    const wasmRoot = new URL("./vendor/wasm", self.location.href).href.replace(/\/$/, "");
    visionInstance = await FilesetResolver.forVisionTasks(wasmRoot);
    landmarkerOptions = {
      runningMode: "VIDEO",
      numHands: 2,
      minHandDetectionConfidence: 0.42,
      minHandPresenceConfidence: 0.4,
      minTrackingConfidence: 0.36,
    };
    modelAssetUrl = new URL("./vendor/models/hand_landmarker.task", self.location.href).href;

    // 先试 GPU：在偏弱的设备上推理通常比 CPU 快数倍；
    // 环境不支持或初始化卡住时回落 CPU，运行中发现 GPU 反而更慢还会再切回 CPU。
    try {
      landmarker = await Promise.race([
        buildLandmarker("GPU"),
        new Promise((_, reject) => setTimeout(() => reject(new Error("GPU init timeout")), 10000)),
      ]);
      delegateUsed = "GPU";
    } catch {
      landmarker = await buildLandmarker("CPU");
      delegateUsed = "CPU";
    }

    self.postMessage({
      type: "ready",
      supportsTrackProcessor: typeof MediaStreamTrackProcessor !== "undefined",
      delegate: delegateUsed,
    });
  } catch (error) {
    self.postMessage({
      type: "error",
      message: error instanceof Error ? error.message : String(error),
    });
  } finally {
    initializing = false;
  }
}

function resetFramePipeline() {
  if (pendingFrame) {
    pendingFrame.close();
    pendingFrame = null;
  }
  readPromise = null;
  readResult = null;
}

async function stopTrack() {
  streamGeneration += 1;
  resetFramePipeline();
  if (streamReader) {
    await streamReader.cancel().catch(() => {});
    streamReader = null;
  }
  if (activeTrack) {
    activeTrack.stop();
    activeTrack = null;
  }
}

function startRead() {
  if (!readPromise) {
    const promise = streamReader.read().then((result) => {
      // 切换摄像头/重启流之后，旧读取的迟到结果不能污染新流
      if (readPromise === promise) readResult = result;
      return result;
    });
    readPromise = promise;
  }
  return readPromise;
}

function takeReadResult() {
  const result = readResult;
  readResult = null;
  readPromise = null;
  if (!result || result.done) return null;
  return result.value || null;
}

// 不阻塞的“下一轮”信号：MessageChannel 没有 setTimeout(0) 的 4ms 钳制，
// 用来判断队列里是否还有已经到达的帧。每次新建通道并及时关闭，避免句柄泄漏。
function tick() {
  if (typeof MessageChannel === "undefined") {
    return new Promise((resolve) => setTimeout(resolve, 0));
  }
  return new Promise((resolve) => {
    const channel = new MessageChannel();
    channel.port1.onmessage = () => {
      channel.port1.close();
      channel.port2.close();
      resolve();
    };
    channel.port2.postMessage(0);
  });
}

// allowWait=true 时等下一帧；false 时只取“已经到达”的帧，绝不空等。
async function nextFrame(allowWait) {
  if (pendingFrame) {
    const frame = pendingFrame;
    pendingFrame = null;
    return frame;
  }
  const read = startRead();
  if (readResult) return takeReadResult();

  if (!allowWait) {
    const timedOut = await Promise.race([read.then(() => false), tick().then(() => true)]);
    if (timedOut && !readResult) return null;
  } else if (!readResult) {
    await read;
  }
  return takeReadResult();
}

// 只取“最新”的一帧。识别比采集慢时队列里会积压旧帧，
// 直接处理旧帧会让手势与星轨落后半秒以上；这里把已经排队
// 的旧帧丢掉（不额外等待），保证每轮推理用的都尽量是最新的帧。
async function freshestFrame() {
  let frame = await nextFrame(true);
  if (!frame) return null;
  for (let index = 0; index < MAX_DRAIN; index += 1) {
    const candidate = await nextFrame(false);
    if (!candidate) break;
    frame.close();
    frame = candidate;
  }
  return frame;
}

async function downgradeToCpu() {
  try {
    landmarker = await buildLandmarker("CPU");
    delegateUsed = "CPU";
    detectMsAverage = 0;
    detectCount = 0;
    self.postMessage({ type: "delegate-change", delegate: "CPU" });
  } catch {
    // 切换失败就继续用当前 delegate
  }
}

async function processTrack(track) {
  await stopTrack();
  if (typeof MediaStreamTrackProcessor === "undefined") {
    track.stop();
    self.postMessage({ type: "stream-error", message: "Video stream processing is unavailable" });
    return;
  }

  activeTrack = track;
  const generation = streamGeneration;
  const processor = new MediaStreamTrackProcessor({ track });
  streamReader = processor.readable.getReader();
  let lastDetectionAt = -Infinity;

  try {
    while (generation === streamGeneration) {
      const frame = await freshestFrame();
      if (!frame) break;

      const timestamp = Number(frame.timestamp) / 1000;
      if (timestamp - lastDetectionAt < DETECT_INTERVAL) {
        frame.close();
        continue;
      }
      lastDetectionAt = timestamp;

      const startedAt = performance.now();
      try {
        const result = landmarker.detectForVideo(frame, timestamp);
        recordDetect(performance.now() - startedAt);
        self.postMessage({
          type: "result",
          landmarks: result.landmarks || [],
          handedness: result.handedness || [],
        });
      } finally {
        frame.close();
      }

      if (!delegateSettled && detectCount >= 20) {
        delegateSettled = true;
        if (delegateUsed === "GPU" && detectMsAverage > GPU_DOWNGRADE_MS) {
          await downgradeToCpu();
        }
      }

      if (detectCount > 0 && detectCount % 20 === 0) reportStats();
    }
  } catch (error) {
    if (generation === streamGeneration) {
      self.postMessage({
        type: "stream-error",
        message: error instanceof Error ? error.message : String(error),
      });
    }
  } finally {
    if (generation === streamGeneration) {
      resetFramePipeline();
      streamReader = null;
      if (activeTrack) activeTrack.stop();
      activeTrack = null;
    }
  }
}

self.addEventListener("message", async (event) => {
  const message = event.data;
  if (message.type === "init") {
    await initialize();
    return;
  }
  if (message.type === "start-track") {
    if (!landmarker) await initialize();
    if (landmarker) {
      await processTrack(message.track);
    } else {
      message.track.stop();
    }
    return;
  }
  if (message.type === "stop-track") {
    await stopTrack();
    return;
  }
  if (message.type !== "detect" || !landmarker) return;

  const startedAt = performance.now();
  try {
    const result = landmarker.detectForVideo(message.bitmap, message.timestamp);
    recordDetect(performance.now() - startedAt);
    message.bitmap.close();
    self.postMessage({
      type: "result",
      landmarks: result.landmarks || [],
      handedness: result.handedness || [],
    });
  } catch (error) {
    message.bitmap.close();
    self.postMessage({
      type: "detect-error",
      message: error instanceof Error ? error.message : String(error),
    });
  }
});
