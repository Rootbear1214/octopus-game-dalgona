/* Dalgona Tracer - vanilla JS */
// Utilities
const $ = (sel) => document.querySelector(sel);
const clamp = (n, a, b) => Math.max(a, Math.min(b, n));
const lerp = (a, b, t) => a + (b - a) * t;

// Cookie helpers (fallback to localStorage when cookies are unavailable, e.g., file://)
let __cookieSupport;
function cookiesEnabled() {
  if (__cookieSupport !== undefined) return __cookieSupport;
  try {
    document.cookie = 'cookietest=1; samesite=lax';
    __cookieSupport = document.cookie.includes('cookietest=');
    // clear test cookie
    document.cookie = 'cookietest=; expires=Thu, 01 Jan 1970 00:00:00 GMT; path=/';
  } catch (_) {
    __cookieSupport = false;
  }
  return __cookieSupport;
}
const COOKIE_NS = 'cookie:';
function setCookie(name, value, days = 365) {
  if (cookiesEnabled()) {
    const d = new Date();
    d.setTime(d.getTime() + days * 24 * 60 * 60 * 1000);
    document.cookie = `${name}=${encodeURIComponent(value)}; expires=${d.toUTCString()}; path=/; samesite=lax`;
  } else {
    try { localStorage.setItem(COOKIE_NS + name, String(value)); } catch (_) {}
  }
}
function getCookie(name) {
  if (cookiesEnabled()) {
    return document.cookie
      .split(';')
      .map((c) => c.trim())
      .filter((c) => c.startsWith(name + '='))
      .map((c) => decodeURIComponent(c.split('=')[1]))[0];
  }
  try { return localStorage.getItem(COOKIE_NS + name) || undefined; } catch (_) { return undefined; }
}

// UI elements
const canvas = $('#game');
const ctx = canvas.getContext('2d');
const timeEl = $('#time');
const cracksEl = $('#cracks');
const scoreEl = $('#score');
const bestEl = $('#best');
const playerNameInput = $('#playerName');
const saveNameBtn = $('#saveName');
const newGameBtn = $('#newGame');
const shapeBtn = $('#shapeBtn');
const cookieBanner = $('#cookieBanner');
const acceptCookiesBtn = $('#acceptCookies');
const declineCookiesBtn = $('#declineCookies');

// Game state
let W = canvas.width;
let H = canvas.height;
let scale = window.devicePixelRatio || 1;
canvas.width = W * scale;
canvas.height = H * scale;
canvas.style.width = W + 'px';
canvas.style.height = H + 'px';
ctx.scale(scale, scale);

const STATE = { idle: 'idle', playing: 'playing', fail: 'fail', done: 'done' };
const SHAPES = ['circle', 'triangle', 'star'];
let currentShapeIdx = 0;
let band = 18; // safe band thickness
let cracks = 0;
let maxCracks = 3;
let startTime = 0;
let timeLimit = 60.0; // seconds
let elapsed = 0;
let state = STATE.idle;
let started = false;
let bestScore = Number(localStorage.getItem('bestScore') || '0');
let lastCrackAt = 0;
let startLen = 0; // where along the path the user started

let path = [];
let pathLength = 0;
let tracePts = [];
let crackPolylines = [];

// Path helpers
function dist(a, b) { const dx = a.x - b.x, dy = a.y - b.y; return Math.hypot(dx, dy); }
function lerpPt(a, b, t) { return { x: lerp(a.x, b.x, t), y: lerp(a.y, b.y, t) }; }

function polylineLength(pts) {
  let L = 0; for (let i = 1; i < pts.length; i++) L += dist(pts[i - 1], pts[i]); return L;
}
function nearestOnSegment(p, a, b) {
  const abx = b.x - a.x, aby = b.y - a.y;
  const apx = p.x - a.x, apy = p.y - a.y;
  const ab2 = abx * abx + aby * aby;
  const t = ab2 === 0 ? 0 : clamp((apx * abx + apy * aby) / ab2, 0, 1);
  const q = { x: a.x + abx * t, y: a.y + aby * t };
  return { q, t, d: dist(p, q) };
}
function nearestOnPolyline(p, pts) {
  let best = { d: Infinity, q: pts[0], seg: 0, t: 0, len: 0 };
  let acc = 0;
  for (let i = 1; i < pts.length; i++) {
    const a = pts[i - 1], b = pts[i];
    const res = nearestOnSegment(p, a, b);
    if (res.d < best.d) {
      best = { d: res.d, q: res.q, seg: i - 1, t: res.t, len: acc + dist(a, res.q) };
    }
    acc += dist(a, b);
  }
  return best;
}

function makeCircle(cx, cy, r, n = 200) {
  const pts = []; for (let i = 0; i <= n; i++) { const t = (i / n) * Math.PI * 2; pts.push({ x: cx + Math.cos(t) * r, y: cy + Math.sin(t) * r }); } return pts;
}
function makeTriangle(cx, cy, r) {
  const pts = [];
  for (let i = 0; i <= 3; i++) {
    const t = (-Math.PI / 2) + (i % 3) * (2 * Math.PI / 3);
    pts.push({ x: cx + Math.cos(t) * r, y: cy + Math.sin(t) * r });
  }
  // densify
  return densify(pts, 6);
}
function makeStar(cx, cy, rOuter, rInner = rOuter * 0.45, spikes = 5) {
  const pts = [];
  const step = Math.PI / spikes;
  let rot = -Math.PI / 2;
  for (let i = 0; i < spikes * 2; i++) {
    const r = i % 2 === 0 ? rOuter : rInner;
    pts.push({ x: cx + Math.cos(rot) * r, y: cy + Math.sin(rot) * r });
    rot += step;
  }
  pts.push(pts[0]);
  return densify(pts, 5);
}
function densify(pts, segsPer = 4) {
  const out = [];
  for (let i = 1; i < pts.length; i++) {
    const a = pts[i - 1], b = pts[i];
    for (let s = 0; s < segsPer; s++) out.push(lerpPt(a, b, s / segsPer));
  }
  out.push(pts[pts.length - 1]);
  return out;
}

function generatePath(kind) {
  const cx = W / 2, cy = H / 2, r = Math.min(W, H) * 0.35;
  if (kind === 'circle') return makeCircle(cx, cy, r);
  if (kind === 'triangle') return makeTriangle(cx, cy, r);
  return makeStar(cx, cy, r);
}

// Game control
function reset() {
  cracks = 0;
  elapsed = 0;
  started = false;
  state = STATE.idle;
  path = generatePath(SHAPES[currentShapeIdx]);
  pathLength = polylineLength(path);
  tracePts = [];
  crackPolylines = [];
  startLen = 0;
  updateHUD();
  draw();
}

function startGame() {
  state = STATE.playing;
  started = false; // will become true on valid pointerdown near start
  startTime = performance.now();
  lastCrackAt = 0;
}

function endGame(success) {
  state = success ? STATE.done : STATE.fail;
  const timeLeft = Math.max(0, timeLimit - elapsed);
  const accuracy = clamp(1 - cracks / maxCracks, 0, 1);
  const score = Math.max(0, Math.round(timeLeft * 20 + accuracy * 800));
  scoreEl.textContent = String(score);
  if (score > bestScore) {
    bestScore = score;
    localStorage.setItem('bestScore', String(bestScore));
    bestEl.classList.add('flash');
    setTimeout(() => bestEl.classList.remove('flash'), 800);
  }
  bestEl.textContent = String(bestScore);
}

function updateHUD() {
  timeEl.textContent = (Math.max(0, timeLimit - elapsed)).toFixed(1);
  cracksEl.textContent = String(cracks);
  bestEl.textContent = String(bestScore);
}

// Rendering
function drawPath(ctx, pts, stroke, width) {
  ctx.beginPath();
  ctx.moveTo(pts[0].x, pts[0].y);
  for (let i = 1; i < pts.length; i++) ctx.lineTo(pts[i].x, pts[i].y);
  ctx.strokeStyle = stroke;
  ctx.lineWidth = width;
  ctx.lineJoin = 'round';
  ctx.lineCap = 'round';
  ctx.stroke();
}

function draw(pointer) {
  ctx.clearRect(0, 0, W, H);
  // background grid
  ctx.save();
  ctx.globalAlpha = 0.15;
  const step = 40;
  ctx.strokeStyle = '#20263a';
  ctx.lineWidth = 1;
  for (let x = (W % step); x < W; x += step) { ctx.beginPath(); ctx.moveTo(x, 0); ctx.lineTo(x, H); ctx.stroke(); }
  for (let y = (H % step); y < H; y += step) { ctx.beginPath(); ctx.moveTo(0, y); ctx.lineTo(W, y); ctx.stroke(); }
  ctx.restore();

  // safe band
  drawPath(ctx, path, 'rgba(125, 211, 252, 0.18)', band);
  // center guide
  drawPath(ctx, path, 'rgba(96, 165, 250, 0.9)', 2);

  // start marker
  const start = path[0];
  ctx.fillStyle = '#10b981';
  ctx.beginPath(); ctx.arc(start.x, start.y, 8, 0, Math.PI * 2); ctx.fill();

  // draw user progress trace
  if (tracePts.length > 1) {
    drawPath(ctx, tracePts, 'rgba(250, 204, 21, 0.95)', 3); // yellow trace
  }

  // draw cracks overlay
  if (crackPolylines.length) {
    ctx.save();
    ctx.strokeStyle = 'rgba(239, 68, 68, 0.95)';
    ctx.lineWidth = 2;
    ctx.lineJoin = 'round';
    ctx.lineCap = 'round';
    for (const poly of crackPolylines) {
      drawPath(ctx, poly, ctx.strokeStyle, ctx.lineWidth);
    }
    ctx.restore();
  }

  if (pointer) {
    ctx.fillStyle = 'white';
    ctx.beginPath(); ctx.arc(pointer.x, pointer.y, 3, 0, Math.PI * 2); ctx.fill();
  }
}

// Pointer handling
let pointer = { x: 0, y: 0, down: false, progressLen: 0 };
function canvasPos(evt) {
  const r = canvas.getBoundingClientRect();
  const x = (evt.clientX - r.left) * (W / r.width);
  const y = (evt.clientY - r.top) * (H / r.height);
  return { x, y };
}

canvas.addEventListener('pointerdown', (e) => {
  const p = canvasPos(e);
  const start = path[0];
  const near = nearestOnPolyline(p, path);
  if (dist(p, start) <= band || near.d <= band * 0.5) {
    pointer = { x: p.x, y: p.y, down: true, progressLen: near.len };
    started = true;
    if (state !== STATE.playing) startGame();
    tracePts = [ { x: p.x, y: p.y } ];
    startLen = near.len;
  }
  draw(p);
});
canvas.addEventListener('pointermove', (e) => {
  const p = canvasPos(e);
  if (pointer.down && state === STATE.playing) {
    const near = nearestOnPolyline(p, path);
    pointer.x = p.x; pointer.y = p.y; pointer.progressLen = near.len;

    // out of band -> crack (cooldown to avoid spam)
    if (near.d > band * 0.5) {
      const now = performance.now();
      if (now - lastCrackAt > 300) {
        cracks = clamp(cracks + 1, 0, maxCracks);
        cracksEl.textContent = String(cracks);
        lastCrackAt = now;
        cracksEl.classList.add('flash');
        setTimeout(() => cracksEl.classList.remove('flash'), 800);
        addCracks(p);
        if (cracks >= maxCracks) endGame(false);
      }
    }

    // finish check: require full loop from where the player started
    const progressed = (near.len - startLen + pathLength) % pathLength;
    if (progressed >= pathLength - 12) {
      endGame(true);
    }

    // record progress trace (throttle points)
    if (!tracePts.length || dist(tracePts[tracePts.length - 1], p) > 2) {
      tracePts.push({ x: p.x, y: p.y });
      if (tracePts.length > 2000) tracePts.shift();
    }
  }
  draw(p);
});
canvas.addEventListener('pointerup', () => { pointer.down = false; });
canvas.addEventListener('pointerleave', () => { pointer.down = false; });

// Game loop for timer
function tick(ts) {
  if (state === STATE.playing) {
    if (!started) startTime = ts; // wait until valid start
    elapsed = (ts - startTime) / 1000;
    if (elapsed >= timeLimit) { endGame(false); }
    updateHUD();
  }
  requestAnimationFrame(tick);
}
requestAnimationFrame(tick);

// Controls
newGameBtn.addEventListener('click', () => { reset(); startGame(); });
shapeBtn.addEventListener('click', () => {
  currentShapeIdx = (currentShapeIdx + 1) % SHAPES.length;
  reset();
});

saveNameBtn.addEventListener('click', () => {
  const name = (playerNameInput.value || '').trim().slice(0, 20);
  if (!name) return;
  if (getCookie('consent') === 'true') setCookie('player', name);
  saveNameBtn.classList.add('flash');
  setTimeout(() => saveNameBtn.classList.remove('flash'), 800);
});

// Cookies banner
function initCookies() {
  const consent = getCookie('consent');
  if (!consent) cookieBanner.classList.remove('hidden');
  if (consent === 'true') {
    const player = getCookie('player');
    if (player) playerNameInput.value = player;
  }
}
acceptCookiesBtn.addEventListener('click', () => {
  setCookie('consent', 'true');
  cookieBanner.classList.add('hidden');
  // if a name is already in the box, persist it
  if (playerNameInput.value) setCookie('player', playerNameInput.value.trim().slice(0, 20));
});
declineCookiesBtn.addEventListener('click', () => {
  setCookie('consent', 'false');
  cookieBanner.classList.add('hidden');
});

// Init
function init() {
  bestEl.textContent = String(bestScore);
  reset();
  initCookies();
}
init();

// Crack generation
function addCracks(p) {
  const branches = 1 + Math.floor(Math.random() * 3); // 1-3 branches
  const cx = W / 2, cy = H / 2;
  for (let b = 0; b < branches; b++) {
    const baseAngle = Math.atan2(p.y - cy, p.x - cx) + (Math.random() * 1.2 - 0.6);
    const segs = 8 + Math.floor(Math.random() * 6); // 8-13 segments
    let ang = baseAngle;
    let step = 8 + Math.random() * 10;
    const poly = [ { x: p.x, y: p.y } ];
    for (let i = 0; i < segs; i++) {
      ang += (Math.random() - 0.5) * 0.6; // jitter
      step *= 0.95 + Math.random() * 0.1;
      const last = poly[poly.length - 1];
      const nx = clamp(last.x + Math.cos(ang) * step, 0, W);
      const ny = clamp(last.y + Math.sin(ang) * step, 0, H);
      poly.push({ x: nx, y: ny });
      // stop early if near bounds
      if (nx <= 2 || ny <= 2 || nx >= W - 2 || ny >= H - 2) break;
    }
    crackPolylines.push(poly);
    if (crackPolylines.length > 200) crackPolylines.splice(0, crackPolylines.length - 200);
  }
}
