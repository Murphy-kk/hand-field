const canvas = document.querySelector("#field");
const ctx = canvas.getContext("2d", { alpha: false });
const previewCanvas = document.querySelector("#previewCanvas");
const previewContext = previewCanvas.getContext("2d");
const video = document.createElement("video");
video.autoplay = true;
video.muted = true;
video.playsInline = true;

const ui = {
  intro: document.querySelector("#intro"),
  cameraToggle: document.querySelector("#cameraToggle"),
  cameraToggleLabel: document.querySelector("#cameraToggleLabel"),
  cameraBtn: document.querySelector("#cameraBtn"),
  demoBtn: document.querySelector("#demoBtn"),
  stopCameraBtn: document.querySelector("#stopCameraBtn"),
  fullscreenBtn: document.querySelector("#fullscreenBtn"),
  helpBtn: document.querySelector("#helpBtn"),
  closeHelpBtn: document.querySelector("#closeHelpBtn"),
  helpDialog: document.querySelector("#helpDialog"),
  statusDot: document.querySelector("#statusDot"),
  statusText: document.querySelector("#statusText"),
  handState: document.querySelector("#handState"),
  gestureState: document.querySelector("#gestureState"),
  fpsState: document.querySelector("#fpsState"),
  hud: document.querySelector("#hud"),
  cameraPanel: document.querySelector("#cameraPanel"),
  gestureHint: document.querySelector("#gestureHint"),
  gestureHintText: document.querySelector("#gestureHintText"),
  shortcutStrip: document.querySelector("#shortcutStrip"),
  toast: document.querySelector("#toast"),
};

const HAND_CONNECTIONS = [
  [0, 1],
  [1, 2],
  [2, 3],
  [3, 4],
  [0, 5],
  [5, 6],
  [6, 7],
  [7, 8],
  [5, 9],
  [9, 10],
  [10, 11],
  [11, 12],
  [9, 13],
  [13, 14],
  [14, 15],
  [15, 16],
  [13, 17],
  [17, 18],
  [18, 19],
  [19, 20],
  [0, 17],
];

let width = 0;
let height = 0;
let dpr = 1;
let handWorker = null;
let handWorkerPromise = null;
let handDetectionBusy = false;
let usingWorkerStream = false;
let stream = null;
let mode = "idle";
let cameraState = "off";
let cameraRequestId = 0;
let hands = [];
let pointerHand = null;
let lastVideoTime = -1;
let lastDetectionAt = -Infinity;
let detectionFrame = 0;
let lastFrameAt = performance.now();
let fpsAverage = 60;
let openGlow = 0;
let toastTimer = null;
let reducedMotion = window.matchMedia("(prefers-reduced-motion: reduce)").matches;

const particles = [];
const stars = [];
const handTrails = new Map();
const starLayer = document.createElement("canvas");
const starContext = starLayer.getContext("2d");
const trailSprite = document.createElement("canvas");
trailSprite.width = 64;
trailSprite.height = 64;
const trailSpriteContext = trailSprite.getContext("2d");
const trailSpriteGradient = trailSpriteContext.createRadialGradient(32, 32, 0, 32, 32, 32);
trailSpriteGradient.addColorStop(0, "rgba(226, 253, 255, 0.95)");
trailSpriteGradient.addColorStop(0.12, "rgba(126, 233, 255, 0.7)");
trailSpriteGradient.addColorStop(0.42, "rgba(63, 176, 235, 0.22)");
trailSpriteGradient.addColorStop(1, "rgba(28, 93, 146, 0)");
trailSpriteContext.fillStyle = trailSpriteGradient;
trailSpriteContext.fillRect(0, 0, 64, 64);
const headSprite = document.createElement("canvas");
headSprite.width = 64;
headSprite.height = 64;
const headSpriteContext = headSprite.getContext("2d");
const headSpriteGradient = headSpriteContext.createRadialGradient(32, 32, 0, 32, 32, 32);
headSpriteGradient.addColorStop(0, "rgba(232, 252, 255, 1)");
headSpriteGradient.addColorStop(0.16, "rgba(166, 244, 255, 0.94)");
headSpriteGradient.addColorStop(0.46, "rgba(67, 177, 255, 0.36)");
headSpriteGradient.addColorStop(1, "rgba(28, 92, 180, 0)");
headSpriteContext.fillStyle = headSpriteGradient;
headSpriteContext.fillRect(0, 0, 64, 64);
const particleCount = reducedMotion ? 850 : 2200;
const ambientStarCount = reducedMotion ? 6500 : 22000;
let handDetectionInterval = 1000 / 30;
const handDetectionIntervalMin = 1000 / 30;
const handDetectionIntervalMax = 1000 / 12;
const trailLifetime = 3200;
const trailDistanceLimit = 520;
const TAU = Math.PI * 2;

// 手势判定不再依赖单帧结果：
// 1) 进入与退出使用两套阈值（迟滞），避免临界抖动；
// 2) 需要连续稳定一段时间才提交（时间确认）；
// 3) 捏合与张开全局互斥，切换后带冷却（过渡延迟）；
// 4) 双手靠近时提高确认门槛，专门压制这一场景下的互相污染。
const GESTURE = {
  pinchEnter: 0.62,
  pinchExit: 0.8,
  openEnter: 1.86,
  openExit: 1.52,
  confirmMs: { pinch: 110, open: 160 },
  releaseMs: { pinch: 100, open: 140 },
  switchCooldownMs: 260,
  nearHandRatio: 0.32,
  nearConfirmBonusMs: 90,
  scatterCooldownMs: 700,
};

const gestureLock = { kind: null, lastKind: null, changedAt: -Infinity };
let scatterCooldownUntil = -Infinity;
let detectSentAt = 0;

function random(min, max) {
  return min + Math.random() * (max - min);
}

function gaussian() {
  let u = 0;
  let v = 0;
  while (u === 0) u = Math.random();
  while (v === 0) v = Math.random();
  return Math.sqrt(-2 * Math.log(u)) * Math.cos(TAU * v);
}

function safeRadius(value, fallback = 0.5) {
  return Number.isFinite(value) && value > 0 ? value : fallback;
}

function createParticle(index) {
  return {
    x: 0,
    y: 0,
    vx: 0,
    vy: 0,
    ox: 0,
    oy: 0,
    size: random(0.36, 1.3),
    phase: random(0, TAU),
    drift: random(0.2, 1.1),
    tone: "cyan",
    alpha: random(0.12, 0.66),
    depth: random(0.3, 1),
    owner: index % 2,
    glow: index % 11 === 0,
  };
}

function seedParticles() {
  particles.length = 0;
  stars.length = 0;
  seedAmbientSky();

  for (let index = 0; index < particleCount; index += 1) {
    particles.push(createParticle(index));
  }

  for (let index = 0; index < 480; index += 1) {
    stars.push({
      x: Math.random() * width,
      y: Math.random() * height,
      radius: random(0.2, 0.9),
      alpha: random(0.04, 0.24),
      phase: random(0, TAU),
    });
  }

  resetParticleOrigins();
}

function seedAmbientSky() {
  starLayer.width = Math.max(1, Math.ceil(width));
  starLayer.height = Math.max(1, Math.ceil(height));
  starContext.clearRect(0, 0, starLayer.width, starLayer.height);

  for (let index = 0; index < ambientStarCount; index += 1) {
    const x = Math.random() * starLayer.width;
    const y = Math.random() * starLayer.height;
    const depth = Math.random();
    const radius = depth > 0.985 ? random(0.9, 1.5) : depth > 0.82 ? random(0.5, 0.9) : random(0.2, 0.58);
    const alpha =
      depth > 0.985 ? random(0.26, 0.58) : depth > 0.82 ? random(0.12, 0.34) : random(0.035, 0.2);
    starContext.fillStyle =
      index % 23 === 0
        ? `rgba(185, 235, 255, ${alpha})`
        : index % 11 === 0
          ? `rgba(118, 203, 255, ${alpha})`
          : `rgba(183, 230, 255, ${alpha})`;
    starContext.beginPath();
    starContext.arc(x, y, radius, 0, TAU);
    starContext.fill();
  }

  const haze = starContext.createRadialGradient(
    width * 0.6,
    height * 0.46,
    0,
    width * 0.6,
    height * 0.46,
    Math.max(width, height) * 0.62,
  );
  haze.addColorStop(0, "rgba(65, 152, 198, 0.035)");
  haze.addColorStop(0.42, "rgba(49, 104, 164, 0.018)");
  haze.addColorStop(1, "rgba(18, 36, 72, 0)");
  starContext.fillStyle = haze;
  starContext.fillRect(0, 0, width, height);
}

function resetParticleOrigins(scatter = false) {
  const minSide = Math.min(width, height);
  const centerX = width * 0.62;
  const centerY = height * 0.5;

  for (let index = 0; index < particles.length; index += 1) {
    const particle = particles[index];
    const angle = random(0, TAU);
    const radius = Math.pow(Math.random(), 0.62) * minSide * 0.48;
    const spiral = angle + radius * 0.0065 + (index % 4) * 0.28;
    particle.ox = centerX + Math.cos(spiral) * radius * 1.56;
    particle.oy = centerY + Math.sin(angle) * radius * 0.68;

    if (scatter) {
      particle.x = random(0, width);
      particle.y = random(0, height);
    } else {
      particle.x = particle.ox + gaussian() * 18;
      particle.y = particle.oy + gaussian() * 12;
    }
    particle.vx = random(-0.08, 0.08);
    particle.vy = random(-0.08, 0.08);
  }
}

function resize() {
  const rect = canvas.getBoundingClientRect();
  width = rect.width;
  height = rect.height;
  dpr = Math.min(window.devicePixelRatio || 1, 1.25);
  canvas.width = Math.max(1, Math.floor(width * dpr));
  canvas.height = Math.max(1, Math.floor(height * dpr));
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  seedParticles();
}

function showToast(message, kind = "info") {
  clearTimeout(toastTimer);
  ui.toast.textContent = message;
  ui.toast.classList.toggle("error", kind === "error");
  ui.toast.classList.add("visible");
  toastTimer = setTimeout(() => ui.toast.classList.remove("visible"), 3200);
}

function setMode(nextMode) {
  mode = nextMode;
  const live = nextMode === "camera";
  const demo = nextMode === "pointer";
  const active = live || demo;

  ui.statusText.textContent = live ? "摄像头已连接" : demo ? "鼠标演示中" : "等待启动";
  ui.statusDot.classList.toggle("live", live);
  ui.statusDot.classList.toggle("demo", demo);
  ui.hud.classList.toggle("visible", active);
  ui.cameraPanel.classList.toggle("hidden", !live);
  ui.gestureHint.classList.toggle("hidden", !active);
  ui.shortcutStrip.classList.toggle("hidden", active);
  ui.intro.classList.toggle("leaving", active);
  ui.handState.textContent = live ? "寻找手部" : demo ? "鼠标模拟" : "等待手势";
  ui.gestureState.textContent = active ? "待命" : "—";
  ui.gestureHintText.textContent = live
    ? "食指牵引 · 张开扩散 · 捏合聚拢"
    : "移动鼠标划出星尘 · 按住 Shift 模拟捏合";

  if (active) {
    resetParticleOrigins(true);
  }
}

async function createHandLandmarker() {
  if (handWorker) return handWorker;
  if (handWorkerPromise) return handWorkerPromise;

  ui.statusText.textContent = "加载手部模型";
  handWorkerPromise = new Promise((resolve, reject) => {
    const worker = new Worker("./hand-worker.js?v=20261031b");
    const timeout = setTimeout(() => {
      worker.terminate();
      reject(new Error("手部模型初始化超时"));
    }, 60000);

    worker.addEventListener("message", (event) => {
      const message = event.data;
      if (message.type === "ready") {
        clearTimeout(timeout);
        worker.supportsTrackProcessor = message.supportsTrackProcessor === true;
        handWorker = worker;
        resolve(worker);
        return;
      }
      if (message.type === "error") {
        clearTimeout(timeout);
        worker.terminate();
        reject(new Error(message.message || "手部模型初始化失败"));
        return;
      }
      if (message.type === "result") {
        handDetectionBusy = false;
        if (!usingWorkerStream && detectSentAt) {
          const cost = performance.now() - detectSentAt;
          detectSentAt = 0;
          if (cost > 0) {
            handDetectionInterval = Math.min(
              handDetectionIntervalMax,
              Math.max(handDetectionIntervalMin, cost * 1.1),
            );
          }
        }
        if (mode === "camera") {
          applyDetectedHands(message.landmarks || [], message.handedness || []);
        }
      }
      if (message.type === "stats") {
        const cost = Number(message.detectMs) || 0;
        if (cost > 0) {
          handDetectionInterval = Math.min(
            handDetectionIntervalMax,
            Math.max(handDetectionIntervalMin, cost * 1.1),
          );
        }
      }
      if (message.type === "detect-error") {
        handDetectionBusy = false;
        console.warn("Hand detection frame failed", message.message);
      }
      if (message.type === "stream-error") {
        usingWorkerStream = false;
        console.warn("Direct camera stream processing failed", message.message);
      }
    });

    worker.addEventListener("error", (event) => {
      clearTimeout(timeout);
      worker.terminate();
      reject(new Error(event.message || "手部识别线程启动失败"));
    });

    worker.postMessage({ type: "init" });
  }).catch((error) => {
    handWorkerPromise = null;
    throw error;
  });

  return handWorkerPromise;
}

async function startCamera() {
  if (cameraState === "on") return;
  if (!window.isSecureContext || !navigator.mediaDevices?.getUserMedia) {
    setMode("pointer");
    setCameraState("off");
    ui.statusText.textContent = "当前浏览器不支持摄像头";
    showToast(
      "此页面需要在 Edge 或 Chrome 中直接打开 HTTPS 链接。聊天软件内置预览窗口通常不能使用摄像头。",
      "error",
    );
    return;
  }
  const requestId = ++cameraRequestId;
  setCameraState("starting");
  ui.cameraBtn.disabled = true;
  ui.cameraBtn.textContent = "正在请求摄像头…";
  try {
    setCameraState("permission");
    ui.statusText.textContent = "等待摄像头授权";
    ui.cameraBtn.textContent = "请在浏览器中允许摄像头";
    setTimeout(() => {
      if (ui.statusText.textContent === "等待摄像头授权") {
        showToast("请在 Edge 地址栏附近选择“允许”，授予本页面摄像头权限。");
      }
    }, 900);
    const nextStream = await navigator.mediaDevices.getUserMedia({
      audio: false,
      video: {
        facingMode: "user",
        width: { ideal: 640, max: 960 },
        height: { ideal: 360, max: 540 },
        frameRate: { ideal: 30, max: 30 },
      },
    });
    if (requestId !== cameraRequestId) {
      nextStream.getTracks().forEach((track) => track.stop());
      return;
    }
    stream = nextStream;
    video.srcObject = stream;
    await video.play();
    setMode("camera");
    ui.statusText.textContent = "摄像头已连接";
    setCameraState("on");
    showToast("摄像头已打开，正在加载手部识别模型。首次使用可能需要十几秒。");

    await createHandLandmarker();
    if (requestId !== cameraRequestId) return;
    if (handWorker?.supportsTrackProcessor) {
      const inferenceTrack = stream.getVideoTracks()[0].clone();
      usingWorkerStream = true;
      handWorker.postMessage({ type: "start-track", track: inferenceTrack }, [inferenceTrack]);
    }
    ui.statusText.textContent = "摄像头与识别已就绪";
    showToast("手部识别已就绪。抬起手，让掌心进入画面。");
  } catch (error) {
    console.error(error);
    if (requestId !== cameraRequestId) return;
    if (stream) {
      ui.statusText.textContent = "摄像头已打开，识别模型加载失败";
      setCameraState("on");
      showToast("摄像头已打开，但手部识别加载失败。请刷新页面或关闭后重试。", "error");
    } else {
      releaseCameraStream();
      setMode("pointer");
      setCameraState("off");
      showToast(
        "摄像头未能打开。请使用 Edge 或 Chrome 直接打开 HTTPS 链接，并允许摄像头权限。",
        "error",
      );
    }
  } finally {
    ui.cameraBtn.disabled = false;
    ui.cameraBtn.innerHTML = '<span class="camera-icon" aria-hidden="true"></span>启用手势交互';
  }
}

function releaseCameraStream() {
  if (handWorker && usingWorkerStream) {
    handWorker.postMessage({ type: "stop-track" });
  }
  usingWorkerStream = false;
  if (!stream) return;
  for (const track of stream.getTracks()) track.stop();
  stream = null;
  video.srcObject = null;
  hands = [];
  handDetectionBusy = false;
  lastVideoTime = -1;
  previewContext.clearRect(0, 0, previewCanvas.width, previewCanvas.height);
}

function stopCamera({ switchToPointer = true } = {}) {
  cameraRequestId += 1;
  releaseCameraStream();
  setCameraState("off");
  ui.statusText.textContent = "摄像头已关闭";
  ui.cameraBtn.disabled = false;
  ui.cameraBtn.innerHTML = '<span class="camera-icon" aria-hidden="true"></span>启用手势交互';

  if (switchToPointer) {
    pointerHand = pointerHand || {
      x: width * 0.6,
      y: height * 0.48,
      active: false,
      pinch: false,
    };
    setMode("pointer");
  } else {
    setMode("idle");
  }
}

function setCameraState(nextState) {
  cameraState = nextState;
  const isOn = nextState === "on";
  const isStarting = nextState === "starting" || nextState === "permission";
  ui.cameraToggle.dataset.state = nextState;
  ui.cameraToggle.setAttribute("aria-checked", String(isOn));
  ui.cameraToggleLabel.textContent = isOn
    ? "摄像头 开"
    : nextState === "permission"
      ? "允许摄像头…"
      : isStarting
        ? "正在连接…"
        : "摄像头 关";
  ui.cameraToggle.title = isOn || isStarting ? "关闭摄像头（C）" : "开启摄像头（C）";
}

function startPointerMode() {
  if (cameraState !== "off") stopCamera({ switchToPointer: false });
  pointerHand = { x: width * 0.6, y: height * 0.48, active: false, pinch: false };
  setMode("pointer");
  showToast("鼠标演示已开启：移动鼠标划出星尘，按住 Shift 模拟捏合。");
}

function toggleCamera() {
  if (cameraState === "on" || cameraState === "starting" || cameraState === "permission") {
    stopCamera();
    showToast("摄像头已关闭。");
  } else {
    startCamera();
  }
}

function resetField() {
  resetParticleOrigins(true);
  handTrails.clear();
  showToast("星群已重新聚合。");
}

function distance(a, b) {
  return Math.hypot(a.x - b.x, a.y - b.y, (a.z || 0) - (b.z || 0));
}

function createHandState(landmarks, index, handedness = [], previousHand = null) {
  const thumb = landmarks[4];
  const indexTip = landmarks[8];
  const middleTip = landmarks[12];
  const ringTip = landmarks[16];
  const pinkyTip = landmarks[20];
  const wrist = landmarks[0];
  const middleMcp = landmarks[9];
  const scale = Math.max(0.025, distance(wrist, middleMcp));
  const pinchRatio = distance(thumb, indexTip) / scale;
  const openness =
    (distance(wrist, indexTip) +
      distance(wrist, middleTip) +
      distance(wrist, ringTip) +
      distance(wrist, pinkyTip)) /
    (scale * 4);
  const extended = [8, 12, 16, 20].map(
    (tipIndex) =>
      distance(wrist, landmarks[tipIndex]) > distance(wrist, landmarks[tipIndex - 2]) * 1.08,
  );
  const extendedCount = extended.filter(Boolean).length;
  const heldGesture = previousHand?.gesture || "palm";
  const pinchThreshold = heldGesture === "pinch" ? GESTURE.pinchExit : GESTURE.pinchEnter;
  const openThreshold = heldGesture === "open" ? GESTURE.openExit : GESTURE.openEnter;
  const rawPinch = pinchRatio < pinchThreshold;
  const rawOpen = !rawPinch && extendedCount >= 3 && openness > openThreshold;
  const rawPointing =
    !rawPinch && extended[0] && !extended[1] && !extended[2] && !extended[3];
  const x = width * (1 - indexTip.x);
  const y = height * indexTip.y;
  const palm = {
    x: width * (1 - (wrist.x + middleMcp.x) / 2),
    y: height * ((wrist.y + middleMcp.y) / 2),
  };
  const pinchCenter = {
    x: width * (1 - (thumb.x + indexTip.x) / 2),
    y: height * ((thumb.y + indexTip.y) / 2),
  };
  const focus = rawPinch
    ? pinchCenter
    : rawPointing
      ? { x: x * 0.78 + palm.x * 0.22, y: y * 0.78 + palm.y * 0.22 }
      : palm;
  const handednessLabel = handedness?.[0]?.categoryName?.toLowerCase() || "hand";

  return {
    id: `${handednessLabel}-${index}`,
    x: focus.x,
    y: focus.y,
    targetX: focus.x,
    targetY: focus.y,
    targetTipX: x,
    targetTipY: y,
    targetPalmX: palm.x,
    targetPalmY: palm.y,
    tipX: x,
    tipY: y,
    trailX: x,
    trailY: y,
    palmX: palm.x,
    palmY: palm.y,
    gesture: heldGesture,
    previousGesture: heldGesture,
    rawPinch,
    rawOpen,
    rawPointing,
    pinch: heldGesture === "pinch",
    open: heldGesture === "open",
    pointing: heldGesture === "palm" && rawPointing,
    pinchScore: previousHand?.pinchScore || 0,
    openScore: previousHand?.openScore || 0,
    previousDetectedAt: previousHand?.detectedAt || 0,
    stateSince: 0,
    lostAt: 0,
    detectedAt: 0,
    justOpened: false,
    strength: 1,
    landmarks,
  };
}

function updateGestureStates(now) {
  const near =
    hands.length > 1 &&
    distance(
      { x: hands[0].palmX, y: hands[0].palmY },
      { x: hands[1].palmX, y: hands[1].palmY },
    ) <
      Math.min(width, height) * GESTURE.nearHandRatio;

  // 1) 证据累计：偶发噪声帧只让分数回落，不会立刻打断确认过程。
  //    首次出现的手没有上一帧时间，dt 记 0，避免凭空攒够确认分数。
  for (const hand of hands) {
    const gap = hand.previousDetectedAt ? now - hand.previousDetectedAt : 0;
    const dt = Math.max(0, Math.min(80, gap));
    if (hand.rawPinch) hand.pinchScore = Math.min(600, hand.pinchScore + dt);
    else hand.pinchScore = Math.max(0, hand.pinchScore - dt * 1.6);
    if (hand.rawOpen) hand.openScore = Math.min(600, hand.openScore + dt);
    else hand.openScore = Math.max(0, hand.openScore - dt * 1.6);
  }

  // 2) 释放：已提交的手势失去原始支撑后，要等释放延迟结束才真的解除
  for (const hand of hands) {
    if (hand.gesture !== "pinch" && hand.gesture !== "open") {
      hand.lostAt = 0;
      continue;
    }
    const supported = hand.gesture === "pinch" ? hand.rawPinch : hand.rawOpen;
    if (supported) {
      hand.lostAt = 0;
      continue;
    }
    if (!hand.lostAt) hand.lostAt = now;
    const releaseMs =
      hand.gesture === "pinch" ? GESTURE.releaseMs.pinch : GESTURE.releaseMs.open;
    if (now - hand.lostAt >= releaseMs) {
      hand.gesture = "palm";
      hand.lostAt = 0;
    }
  }

  // 3) 先记录“已松手”的时刻：让接下来的相反手势进入过渡冷却，
  //    否则松手与相反手势会在同一帧里无缝换手。
  const heldAfterRelease = hands.some((hand) => hand.gesture === "pinch")
    ? "pinch"
    : hands.some((hand) => hand.gesture === "open")
      ? "open"
      : null;
  if (heldAfterRelease !== gestureLock.kind) {
    gestureLock.kind = heldAfterRelease;
    gestureLock.changedAt = now;
  }

  // 4) 提交：全局互斥（另一只手握着相反手势时直接拒绝）+ 切换冷却 + 靠近加成
  const pinchNeed = GESTURE.confirmMs.pinch + (near ? GESTURE.nearConfirmBonusMs : 0);
  const openNeed = GESTURE.confirmMs.open + (near ? GESTURE.nearConfirmBonusMs : 0);

  for (const hand of hands) {
    const desired =
      hand.pinchScore >= pinchNeed ? "pinch" : hand.openScore >= openNeed ? "open" : null;
    if (!desired || desired === hand.gesture) continue;
    const opposite = desired === "pinch" ? "open" : "pinch";
    if (near && hands.some((other) => other !== hand && other.gesture === opposite)) continue;
    if (
      now - gestureLock.changedAt < GESTURE.switchCooldownMs &&
      gestureLock.lastKind &&
      gestureLock.lastKind !== desired
    ) {
      continue;
    }
    hand.gesture = desired;
    hand.stateSince = now;
    hand.lostAt = 0;
    if (desired === "pinch") hand.openScore = 0;
    else hand.pinchScore = 0;
    gestureLock.kind = desired;
    gestureLock.lastKind = desired;
    gestureLock.changedAt = now;
  }

  // 4.5) 双手靠近时不允许任何形式的并发：保留先建立的手势，解除后建立的那个
  if (near) {
    const pinchHand = hands.find((hand) => hand.gesture === "pinch");
    const openHand = hands.find((hand) => hand.gesture === "open");
    if (pinchHand && openHand) {
      const dropped = openHand.stateSince >= pinchHand.stateSince ? openHand : pinchHand;
      dropped.gesture = "palm";
      dropped.lostAt = 0;
      gestureLock.kind = hands.some((hand) => hand.gesture === "pinch")
        ? "pinch"
        : hands.some((hand) => hand.gesture === "open")
          ? "open"
          : null;
      gestureLock.changedAt = now;
    }
  }

  // 5) 派生标志；张开的“上升沿”同时受扩散冷却约束，避免连环散射
  for (const hand of hands) {
    hand.pinch = hand.gesture === "pinch";
    hand.open = hand.gesture === "open";
    hand.pointing = !hand.pinch && !hand.open && hand.rawPointing;
    const risingOpen = hand.open && hand.previousGesture !== "open";
    hand.justOpened = risingOpen && now >= scatterCooldownUntil;
    if (hand.justOpened) {
      scatterCooldownUntil = now + GESTURE.scatterCooldownMs;
    }
  }
}

function detectHands(now) {
  if (usingWorkerStream) return;
  if (!handWorker || !stream || video.readyState < 2 || handDetectionBusy) return;
  if (video.currentTime === lastVideoTime) return;
  if (now - lastDetectionAt < handDetectionInterval) return;

  lastVideoTime = video.currentTime;
  lastDetectionAt = now;
  handDetectionBusy = true;
  detectionFrame += 1;
  detectSentAt = now;

  createImageBitmap(video, {
    resizeWidth: 384,
    resizeHeight: 216,
    resizeQuality: "low",
  })
    .then((bitmap) => {
      if (!handWorker || mode !== "camera") {
        bitmap.close();
        handDetectionBusy = false;
        return;
      }
      handWorker.postMessage({ type: "detect", bitmap, timestamp: now }, [bitmap]);
    })
    .catch((error) => {
      handDetectionBusy = false;
      console.warn("Could not capture camera frame", error);
    });
}

function applyDetectedHands(landmarksList, handednessList = []) {
  const now = performance.now();
  const previous = new Map(hands.map((hand) => [hand.id, hand]));
  hands = landmarksList.map((landmarks, index) => {
    const label = handednessList[index]?.[0]?.categoryName?.toLowerCase() || "hand";
    const old = previous.get(`${label}-${index}`) || null;
    const next = createHandState(landmarks, index, handednessList[index] || [], old);
    if (old) {
      // 识别到的间隔越长，前馈补偿越大，抵消低帧率设备上的跟随迟滞；
      // 正常 30FPS 时补偿量与原来完全一致（0.16 / 0.24）。
      const gap = old.detectedAt ? Math.min(400, Math.max(0, now - old.detectedAt)) : 33;
      const overGap = Math.max(0, gap - 33);
      const targetLead = Math.min(0.42, 0.16 + overGap / 260);
      const tipLead = Math.min(0.62, 0.24 + overGap / 200);
      const targetVelocityX = next.targetX - old.targetX;
      const targetVelocityY = next.targetY - old.targetY;
      const tipVelocityX = next.targetTipX - old.targetTipX;
      const tipVelocityY = next.targetTipY - old.targetTipY;
      next.targetX += targetVelocityX * targetLead;
      next.targetY += targetVelocityY * targetLead;
      next.targetTipX += tipVelocityX * tipLead;
      next.targetTipY += tipVelocityY * tipLead;
      next.x = old.x;
      next.y = old.y;
      next.tipX = old.tipX;
      next.tipY = old.tipY;
      next.trailX = old.trailX;
      next.trailY = old.trailY;
      next.palmX = old.palmX;
      next.palmY = old.palmY;
    }
    next.detectedAt = now;
    return next;
  });
  hands.sort((left, right) => left.x - right.x);

  updateGestureStates(now);

  ui.handState.textContent =
    hands.length === 0 ? "寻找手部" : hands.length === 1 ? "已识别 1 只手" : "已识别 2 只手";
  const gestureHand = hands.find((hand) => hand.pinch) || hands.find((hand) => hand.open) || hands[0];
  ui.gestureState.textContent = !gestureHand
    ? "待命"
    : gestureHand.pinch
      ? "捏合 / 聚拢"
      : gestureHand.open
        ? "张开 / 扩散"
        : gestureHand.pointing
          ? "食指 / 牵引"
          : "手掌 / 跟随";
  drawPreview(landmarksList);
}

function closeHandWorker() {
  if (handWorker) {
    handWorker.terminate();
    handWorker = null;
    handWorkerPromise = null;
  }
}

function sourceCropRect(videoWidth, videoHeight, targetWidth, targetHeight) {
  const targetRatio = targetWidth / targetHeight;
  const sourceRatio = videoWidth / videoHeight;
  if (sourceRatio > targetRatio) {
    const cropWidth = videoHeight * targetRatio;
    return {
      x: (videoWidth - cropWidth) / 2,
      y: 0,
      width: cropWidth,
      height: videoHeight,
    };
  }
  const cropHeight = videoWidth / targetRatio;
  return {
    x: 0,
    y: (videoHeight - cropHeight) / 2,
    width: videoWidth,
    height: cropHeight,
  };
}

function landmarkToPreview(landmark, crop, targetWidth, targetHeight) {
  const rawX = landmark.x * video.videoWidth;
  const rawY = landmark.y * video.videoHeight;
  return {
    x: ((crop.width - (rawX - crop.x)) / crop.width) * targetWidth,
    y: ((rawY - crop.y) / crop.height) * targetHeight,
  };
}

function drawPreview(landmarksList) {
  const targetWidth = previewCanvas.width;
  const targetHeight = previewCanvas.height;
  previewContext.clearRect(0, 0, targetWidth, targetHeight);

  if (video.readyState < 2) return;
  const crop = sourceCropRect(video.videoWidth, video.videoHeight, targetWidth, targetHeight);
  previewContext.save();
  previewContext.translate(targetWidth, 0);
  previewContext.scale(-1, 1);
  previewContext.drawImage(
    video,
    crop.x,
    crop.y,
    crop.width,
    crop.height,
    0,
    0,
    targetWidth,
    targetHeight,
  );
  previewContext.restore();

  previewContext.save();
  previewContext.fillStyle = "rgba(2, 8, 16, 0.12)";
  previewContext.fillRect(0, 0, targetWidth, targetHeight);

  for (const landmarks of landmarksList) {
    const points = landmarks.map((landmark) =>
      landmarkToPreview(landmark, crop, targetWidth, targetHeight),
    );

    previewContext.strokeStyle = "rgba(122, 229, 255, 0.72)";
    previewContext.lineWidth = 1.5;
    previewContext.shadowColor = "rgba(90, 219, 255, 0.7)";
    previewContext.shadowBlur = 6;
    for (const [from, to] of HAND_CONNECTIONS) {
      previewContext.beginPath();
      previewContext.moveTo(points[from].x, points[from].y);
      previewContext.lineTo(points[to].x, points[to].y);
      previewContext.stroke();
    }
    previewContext.shadowBlur = 0;

    for (let index = 0; index < points.length; index += 1) {
      const point = points[index];
      const isTip = [4, 8, 12, 16, 20].includes(index);
      previewContext.beginPath();
      previewContext.arc(point.x, point.y, isTip ? 3.3 : 1.8, 0, TAU);
      previewContext.fillStyle = isTip ? "#ffd17e" : "#e9fcff";
      previewContext.fill();
    }
  }
  previewContext.restore();
}

function currentHands() {
  if (mode === "camera") return hands;
  if (mode === "pointer" && pointerHand) {
    return [
      {
        ...pointerHand,
        id: "pointer",
        tipX: pointerHand.x,
        tipY: pointerHand.y,
        trailX: pointerHand.x,
        trailY: pointerHand.y,
        palmX: pointerHand.x,
        palmY: pointerHand.y,
        open: false,
        pointing: true,
        strength: 1,
      },
    ];
  }
  return [];
}

function appendTrailPoint(trail, x, y, now) {
  const previous = trail.points.at(-1);
  if (!previous) {
    trail.points.push({
      x,
      y,
      time: now,
      dust: Array.from({ length: 7 }, () => ({
        side: random(-1, 1),
        along: random(-1, 1),
        size: random(0.5, 1.7),
      })),
    });
    return;
  }

  const dx = x - previous.x;
  const dy = y - previous.y;
  const distance = Math.hypot(dx, dy);
  if (distance < 1.5) return;

  const steps = Math.min(64, Math.max(1, Math.ceil(distance / 7)));
  for (let step = 1; step <= steps; step += 1) {
    const progress = step / steps;
    trail.points.push({
      x: previous.x + dx * progress,
      y: previous.y + dy * progress,
      time: now - (1 - progress) * 14,
      dust: Array.from({ length: 7 }, () => ({
        side: random(-1, 1),
        along: random(-1, 1),
        size: random(0.5, 1.7),
      })),
    });
  }
  let trailDistance = 0;
  for (let index = trail.points.length - 1; index > 0; index -= 1) {
    trailDistance += Math.hypot(
      trail.points[index].x - trail.points[index - 1].x,
      trail.points[index].y - trail.points[index - 1].y,
    );
    if (trailDistance > trailDistanceLimit) {
      trail.points.splice(0, index);
      break;
    }
  }
}

function updateHandTrails(activeHands, now) {
  const activeIds = new Set();

  for (const hand of activeHands) {
    if (!hand.pointing) continue;
    const id = hand.id || "pointer";
    activeIds.add(id);

    let trail = handTrails.get(id);
    if (!trail) {
      trail = { points: [], lastSampleAt: -Infinity };
      handTrails.set(id, trail);
    }

    if (now - trail.lastSampleAt < 16) continue;
    trail.lastSampleAt = now;
    appendTrailPoint(trail, hand.targetTipX ?? hand.tipX, hand.targetTipY ?? hand.tipY, now);
  }

  for (const [id, trail] of handTrails) {
    trail.points = trail.points.filter((point) => now - point.time <= trailLifetime);
    if (trail.points.length === 0 && !activeIds.has(id)) {
      handTrails.delete(id);
    }
  }
}

function drawHandTrails(now) {
  ctx.globalCompositeOperation = "lighter";

  for (const trail of handTrails.values()) {
    const points = trail.points;
    if (points.length < 2) continue;
    const distances = new Array(points.length);
    let distanceFromHead = 0;
    distances[points.length - 1] = 0;
    for (let index = points.length - 1; index > 0; index -= 1) {
      distanceFromHead += Math.hypot(
        points[index].x - points[index - 1].x,
        points[index].y - points[index - 1].y,
      );
      distances[index - 1] = distanceFromHead;
    }

    for (let index = 0; index < points.length; index += 1) {
      const point = points[index];
      const timeLife = Math.max(0, 1 - (now - point.time) / trailLifetime);
      const distanceLife = Math.max(0, 1 - distances[index] / trailDistanceLimit);
      const life = Math.min(timeLife, distanceLife);
      if (life <= 0) continue;
      const alpha = Math.pow(life, 1.45);
      const sparkle = 0.72 + Math.sin(now * 0.004 + point.x * 0.13) * 0.28;
      const previousPoint = points[Math.max(0, index - 1)];
      const nextPoint = points[Math.min(points.length - 1, index + 1)];
      const tangentX = nextPoint.x - previousPoint.x;
      const tangentY = nextPoint.y - previousPoint.y;
      const tangentLength = Math.max(1, Math.hypot(tangentX, tangentY));
      const tangentUnitX = tangentX / tangentLength;
      const tangentUnitY = tangentY / tangentLength;
      const normalX = -tangentUnitY;
      const normalY = tangentUnitX;
      const plumeWidth = 4 + (1 - alpha) * 30;

      for (const mote of point.dust) {
        const drawX =
          point.x + normalX * mote.side * plumeWidth + tangentUnitX * mote.along * 5;
        const drawY =
          point.y + normalY * mote.side * plumeWidth + tangentUnitY * mote.along * 5;
        const spriteSize = 5 + mote.size * 4 + alpha * 3;
        ctx.globalAlpha = alpha * 0.16 * sparkle;
        ctx.drawImage(
          trailSprite,
          drawX - spriteSize / 2,
          drawY - spriteSize / 2,
          spriteSize,
          spriteSize,
        );
        if (mote.size > 1.05 || index % 4 === 0) {
          ctx.globalAlpha = alpha * 0.46 * sparkle;
          ctx.fillStyle = "rgba(210, 249, 255, 1)";
          const coreSize = 0.65 + mote.size * 0.75;
          ctx.fillRect(drawX - coreSize / 2, drawY - coreSize / 2, coreSize, coreSize);
        }
      }
    }
    ctx.globalAlpha = 1;
  }

  for (const hand of currentHands()) {
    if (!hand.pointing) continue;
    ctx.globalAlpha = 0.94;
    ctx.drawImage(headSprite, hand.trailX - 23, hand.trailY - 23, 46, 46);
    ctx.globalAlpha = 1;
    ctx.save();
    ctx.translate(hand.trailX, hand.trailY);
    ctx.rotate(now * 0.00055);
    ctx.beginPath();
    for (let point = 0; point < 10; point += 1) {
      const radius = point % 2 === 0 ? 7 : 2.8;
      const angle = -Math.PI / 2 + (point * Math.PI) / 5;
      const x = Math.cos(angle) * radius;
      const y = Math.sin(angle) * radius;
      if (point === 0) ctx.moveTo(x, y);
      else ctx.lineTo(x, y);
    }
    ctx.closePath();
    ctx.fillStyle = "rgba(210, 249, 255, 0.96)";
    ctx.fill();
    ctx.strokeStyle = "rgba(107, 211, 255, 0.62)";
    ctx.lineWidth = 0.8;
    ctx.stroke();
    ctx.restore();
  }

  ctx.globalCompositeOperation = "source-over";
}

function smoothTrackedHands(delta) {
  const blend = Math.min(0.82, 0.58 * Math.max(0.5, delta / 16.667));
  const trailBlend = Math.min(0.95, 0.78 * Math.max(0.5, delta / 16.667));
  for (const hand of hands) {
    hand.x += (hand.targetX - hand.x) * blend;
    hand.y += (hand.targetY - hand.y) * blend;
    hand.tipX += (hand.targetTipX - hand.tipX) * blend;
    hand.tipY += (hand.targetTipY - hand.tipY) * blend;
    hand.trailX += (hand.targetTipX - hand.trailX) * trailBlend;
    hand.trailY += (hand.targetTipY - hand.trailY) * trailBlend;
    hand.palmX += (hand.targetPalmX - hand.palmX) * blend;
    hand.palmY += (hand.targetPalmY - hand.palmY) * blend;
  }
}

function updateParticles(delta) {
  const dt = Math.min(delta / 16.667, 2);
  if (mode === "camera") smoothTrackedHands(delta);
  const activeHands = currentHands();
  const driftTime = performance.now() * 0.00015;
  const scatterHand = activeHands.find((hand) => hand.open && hand.justOpened);

  if (scatterHand) {
    openGlow = 1;
    handTrails.clear();
    for (const particle of particles) {
      particle.x = random(2, Math.max(3, width - 2));
      particle.y = random(2, Math.max(3, height - 2));
      const outX = particle.x - scatterHand.x;
      const outY = particle.y - scatterHand.y;
      const length = Math.max(1, Math.hypot(outX, outY));
      const launchSpeed = random(2.5, 7.5);
      particle.vx = (outX / length) * launchSpeed;
      particle.vy = (outY / length) * launchSpeed;
    }
    for (const hand of activeHands) {
      hand.justOpened = false;
    }
  }

  for (const particle of particles) {
    let ax = (particle.ox - particle.x) * 0.00075;
    let ay = (particle.oy - particle.y) * 0.00075;
    ax += Math.cos(driftTime + particle.phase) * 0.0018 * particle.drift;
    ay += Math.sin(driftTime * 1.2 + particle.phase) * 0.0013 * particle.drift;

    const controllingHands =
      activeHands.length > 1 ? [activeHands[particle.owner % activeHands.length]] : activeHands;

    for (const hand of controllingHands) {
      const dx = hand.x - particle.x;
      const dy = hand.y - particle.y;
      const distanceToHand = Math.max(28, Math.hypot(dx, dy));
      const reach = hand.open || hand.pinch ? Number.POSITIVE_INFINITY : 420;
      if (distanceToHand > reach) continue;

      const falloff = 1 - distanceToHand / reach;
      const nx = dx / distanceToHand;
      const ny = dy / distanceToHand;

      if (hand.open) {
        const push = 0.1 + 0.18 * Math.min(1, distanceToHand / Math.max(width, height));
        particle.vx -= nx * push * dt;
        particle.vy -= ny * push * dt;
      } else if (hand.pinch) {
        const targetSpeed = Math.min(24, distanceToHand * 0.18);
        const follow = 0.2;
        particle.vx += (nx * targetSpeed - particle.vx) * follow * dt;
        particle.vy += (ny * targetSpeed - particle.vy) * follow * dt;
      } else if (hand.pointing) {
        const wakeRadius = 190;
        if (distanceToHand < wakeRadius) {
          const wakeFalloff = 1 - distanceToHand / wakeRadius;
          const push = Math.pow(wakeFalloff, 1.7) * 0.7;
          const drift = Math.sin(particle.phase + driftTime * 6.667) * wakeFalloff * 0.62;
          particle.vx -= nx * push * dt - ny * drift * dt;
          particle.vy -= ny * push * dt + nx * drift * dt;
        }
      } else {
        const targetSpeed = Math.min(14, distanceToHand * 0.1) * falloff;
        const follow = 0.16 * falloff;
        const swirl = 0.8;
        particle.vx += (nx * targetSpeed - particle.vx) * follow * dt - ny * swirl * falloff * dt;
        particle.vy += (ny * targetSpeed - particle.vy) * follow * dt + nx * swirl * falloff * dt;
      }
    }

    particle.vx = (particle.vx + ax * dt) * 0.94;
    particle.vy = (particle.vy + ay * dt) * 0.94;
    const speed = Math.hypot(particle.vx, particle.vy);
    if (speed > 16) {
      particle.vx = (particle.vx / speed) * 16;
      particle.vy = (particle.vy / speed) * 16;
    }
    particle.x += particle.vx * dt;
    particle.y += particle.vy * dt;

    if (
      particle.x < -80 ||
      particle.x > width + 80 ||
      particle.y < -80 ||
      particle.y > height + 80
    ) {
      particle.x = particle.ox;
      particle.y = particle.oy;
      particle.vx = 0;
      particle.vy = 0;
    }
  }

  updateHandTrails(activeHands, performance.now());

}

function drawBackground(now) {
  ctx.globalCompositeOperation = "source-over";
  const gradient = ctx.createRadialGradient(
    width * 0.61,
    height * 0.46,
    0,
    width * 0.61,
    height * 0.46,
    Math.max(width, height) * 0.72,
  );
  gradient.addColorStop(0, "rgba(12, 28, 49, 0.96)");
  gradient.addColorStop(0.36, "rgba(5, 13, 26, 0.98)");
  gradient.addColorStop(1, "rgba(1, 4, 10, 1)");
  ctx.fillStyle = gradient;
  ctx.fillRect(0, 0, width, height);
  ctx.globalAlpha = 1;
  ctx.drawImage(starLayer, 0, 0, width, height);
  if (openGlow > 0.01) {
    ctx.globalCompositeOperation = "lighter";
    ctx.globalAlpha = openGlow * 0.48;
    ctx.drawImage(starLayer, 0, 0, width, height);
    ctx.globalAlpha = 1;
    ctx.globalCompositeOperation = "source-over";
  }

  for (const star of stars) {
    const twinkle = 0.72 + 0.28 * Math.sin(now * 0.0011 + star.phase);
    ctx.fillStyle = `rgba(184, 229, 255, ${star.alpha * twinkle})`;
    ctx.beginPath();
    ctx.arc(star.x, star.y, safeRadius(star.radius, 0.25), 0, TAU);
    ctx.fill();
  }
}

function drawParticles(now) {
  ctx.globalCompositeOperation = "lighter";
  const glowMultiplier = 1 + openGlow * 1.15;
  const sizeMultiplier = 1 + openGlow * 0.3;

  for (const particle of particles) {
    const flicker = 0.68 + Math.sin(now * 0.0016 + particle.phase) * 0.24;
    const alpha = Math.min(
      0.98,
      particle.alpha * flicker * (0.7 + particle.depth * 0.3) * glowMultiplier,
    );
    const color = `rgba(116, 226, 255, ${alpha})`;
    ctx.fillStyle = color;
    const coreSize = Math.max(1, Math.round(particle.size * 1.25 * sizeMultiplier));
    ctx.fillRect(particle.x - coreSize / 2, particle.y - coreSize / 2, coreSize, coreSize);

    if (particle.glow || particle.size > 1.12) {
      ctx.fillStyle = `rgba(90, 213, 255, ${alpha * (0.075 + openGlow * 0.13)})`;
      ctx.beginPath();
      ctx.arc(
        particle.x,
        particle.y,
        safeRadius(particle.size * (4.2 + openGlow * 1.8), 1),
        0,
        TAU,
      );
      ctx.fill();
    }
  }

  const activeHands = currentHands();
  for (const hand of activeHands) {
    const radius = hand.pinch ? 102 : hand.open ? 125 : 72;
    const core = ctx.createRadialGradient(
      hand.x,
      hand.y,
      0,
      hand.x,
      hand.y,
      radius,
    );
    core.addColorStop(0, hand.open ? "rgba(255, 211, 136, 0.32)" : "rgba(157, 239, 255, 0.34)");
    core.addColorStop(0.22, hand.pinch ? "rgba(116, 168, 255, 0.18)" : "rgba(70, 204, 255, 0.11)");
    core.addColorStop(1, "rgba(20, 91, 144, 0)");
    ctx.fillStyle = core;
    ctx.beginPath();
    ctx.arc(hand.x, hand.y, safeRadius(radius, 1), 0, TAU);
    ctx.fill();

    ctx.strokeStyle = hand.pinch ? "rgba(170, 180, 255, 0.46)" : "rgba(117, 227, 255, 0.2)";
    ctx.lineWidth = hand.pinch ? 1.4 : 0.8;
    ctx.beginPath();
    ctx.arc(hand.x, hand.y, hand.pinch ? 17 : 12, 0, TAU);
    ctx.stroke();
  }

  ctx.globalCompositeOperation = "source-over";
}

function render(now) {
  try {
    const delta = now - lastFrameAt;
    lastFrameAt = now;
    if (delta > 0) fpsAverage += (1000 / delta - fpsAverage) * 0.04;
    ui.fpsState.textContent = `${Math.round(fpsAverage)} FPS`;

    if (mode === "camera") detectHands(now);
    const anyOpen = currentHands().some((hand) => hand.open);
    openGlow = anyOpen
      ? Math.min(1, openGlow + Math.min(0.16, Math.max(0.05, delta / 100)))
      : Math.max(0, openGlow - Math.min(0.08, Math.max(0.015, delta / 650)));
    updateParticles(delta);
    drawBackground(now);
  drawHandTrails(now);
    drawParticles(now);
  } catch (error) {
    console.warn("A render frame was skipped", error);
  } finally {
    requestAnimationFrame(render);
  }
}

function updatePointer(event) {
  if (mode !== "pointer" || !pointerHand) return;
  const rect = canvas.getBoundingClientRect();
  pointerHand.x = event.clientX - rect.left;
  pointerHand.y = event.clientY - rect.top;
  pointerHand.active = true;
  pointerHand.pinch = event.shiftKey;
  ui.gestureState.textContent = pointerHand.pinch ? "捏合 / 聚拢" : "鼠标 / 星尘";
}

canvas.addEventListener("pointermove", updatePointer);
canvas.addEventListener("pointerdown", (event) => {
  updatePointer(event);
  if (pointerHand) pointerHand.pinch = event.shiftKey;
  canvas.setPointerCapture?.(event.pointerId);
});
canvas.addEventListener("pointerup", (event) => {
  updatePointer(event);
  if (pointerHand) pointerHand.pinch = false;
});
canvas.addEventListener("pointercancel", () => {
  if (pointerHand) pointerHand.pinch = false;
});

ui.cameraBtn.addEventListener("click", startCamera);
ui.demoBtn.addEventListener("click", startPointerMode);
ui.stopCameraBtn.addEventListener("click", () => {
  stopCamera();
});
ui.cameraToggle.addEventListener("click", toggleCamera);
ui.fullscreenBtn.addEventListener("click", toggleFullscreen);
ui.helpBtn.addEventListener("click", () => ui.helpDialog.showModal());
ui.closeHelpBtn.addEventListener("click", () => ui.helpDialog.close());
ui.helpDialog.addEventListener("click", (event) => {
  if (event.target === ui.helpDialog) ui.helpDialog.close();
});

window.addEventListener("keydown", (event) => {
  if (event.target instanceof HTMLInputElement || event.target instanceof HTMLTextAreaElement) return;
  if (event.repeat) return;
  if (event.key.toLowerCase() === "c") toggleCamera();
  if (event.key.toLowerCase() === "m") startPointerMode();
  if (event.key.toLowerCase() === "r") resetField();
  if (event.key.toLowerCase() === "f") toggleFullscreen();
});

window.addEventListener("resize", resize);
window.addEventListener("beforeunload", () => {
  stopCamera({ switchToPointer: false });
  closeHandWorker();
});

function toggleFullscreen() {
  if (!document.fullscreenElement) {
    document.documentElement.requestFullscreen?.();
  } else {
    document.exitFullscreen?.();
  }
}

resize();
setCameraState("off");
requestAnimationFrame(render);

const params = new URLSearchParams(window.location.search);
if (params.get("demo") === "1") {
  startPointerMode();
}
