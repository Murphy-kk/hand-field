importScripts("./vendor/vision_bundle.js");

const { FilesetResolver, HandLandmarker } = Vision;

let landmarker = null;
let initializing = false;
let streamGeneration = 0;
let streamReader = null;
let activeTrack = null;

async function initialize() {
  if (landmarker) {
    self.postMessage({
      type: "ready",
      supportsTrackProcessor: typeof MediaStreamTrackProcessor !== "undefined",
    });
    return;
  }
  if (initializing) return;
  initializing = true;

  try {
    const wasmRoot = new URL("./vendor/wasm", self.location.href).href.replace(/\/$/, "");
    const vision = await FilesetResolver.forVisionTasks(wasmRoot);
    const commonOptions = {
      runningMode: "VIDEO",
      numHands: 2,
      minHandDetectionConfidence: 0.42,
      minHandPresenceConfidence: 0.4,
      minTrackingConfidence: 0.36,
    };
    const modelAssetPath = new URL(
      "./vendor/models/hand_landmarker.task",
      self.location.href,
    ).href;

    // CPU inference in a worker avoids competing with the particle canvas
    // for the same WebGL context on laptops with integrated graphics.
    landmarker = await HandLandmarker.createFromOptions(vision, {
      ...commonOptions,
      baseOptions: { modelAssetPath, delegate: "CPU" },
    });

    self.postMessage({
      type: "ready",
      supportsTrackProcessor: typeof MediaStreamTrackProcessor !== "undefined",
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

async function stopTrack() {
  streamGeneration += 1;
  if (streamReader) {
    await streamReader.cancel().catch(() => {});
    streamReader = null;
  }
  if (activeTrack) {
    activeTrack.stop();
    activeTrack = null;
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
      const { value: frame, done } = await streamReader.read();
      if (done) break;
      if (!frame) continue;

      const timestamp = Number(frame.timestamp) / 1000;
      if (timestamp - lastDetectionAt < 1000 / 30) {
        frame.close();
        continue;
      }
      lastDetectionAt = timestamp;

      try {
        const result = landmarker.detectForVideo(frame, timestamp);
        self.postMessage({
          type: "result",
          landmarks: result.landmarks || [],
          handedness: result.handedness || [],
        });
      } finally {
        frame.close();
      }
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

  try {
    const result = landmarker.detectForVideo(message.bitmap, message.timestamp);
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
