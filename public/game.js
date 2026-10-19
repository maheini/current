(() => {
'use strict';
const $ = (s, r = document) => r.querySelector(s);
const clamp = (x, a, b) => Math.max(a, Math.min(b, x));
const lerp = (a, b, k) => a + (b - a) * k;
const TAU = Math.PI * 2;
const r1 = x => Math.round(x * 10) / 10;
const r3 = x => Math.round(x * 1000) / 1000;
const fmtHz = f => (f > 0.05 ? r1(f).toFixed(1) : '0') + ' Hz';

/* ---------- Spielregeln ----------
   Seilmodell: Das Seil ist ein geschlossener Kreis wie der Draht im Stromkreis.
   Wechselstrom: Maus hin und her, das Seil fährt hin und her.
   Gleichstrom: Mausrad drehen, das Seil läuft im Kreis.
   Gesägt wird in beiden Fällen, denn die Reibung im Holz braucht nur Bewegung, keine Richtung. */
const CFG = {
  H: 1 / 120,         // feste Rechenschritte, damit alle gleich sägen
  OMEGA: 34,          // so schnell folgt das Seil der Hand
  STROKE: 2,          // ein Tastendruck zieht das Seil 2 Einheiten, bei beiden Stromarten gleich
  BITE: 25,           // so schnell kommt die Kraft eines Zugs im Holz an
  MAX_RATE: 16, BURST: 4, // mehr Seil pro Sekunde zählt nicht: Maus schütteln und Rad wirbeln enden gleich schnell
  MOUSE: 0.011,       // Seil-Einheiten pro Pixel Mausweg (Wechselstrom)
  WHEEL: 0.65,        // Seil-Einheiten pro Rasterstufe am Mausrad (Gleichstrom)
  LEAD: 1.2,          // so weit darf das Mausrad dem Seil vorauslaufen
  VMAX: 16,           // schneller läuft das Seil nicht, sonst scheinen Punkte und Speichen rückwärts zu laufen
  NAIL_SLACK: 0.5,    // so viel Seil darf beim Nagel noch zucken
  CUT: 1 / 22,        // Schnitt pro Seil-Einheit bei einem mittleren Stamm
  FEED_GRACE: 0.3,    // so lange darf das Seil nach dem letzten Schnitt noch auslaufen
  JAM_T: 1.2,         // so lange klemmt ein Stamm, wenn zu früh gesägt wurde
  SLOTS: 4,           // Platz auf dem Band
  LIVES: 3,
  NAIL_T: 1.5, NAIL_GRACE: 0.35, LIFT: 0.95, REPAIR_T: 2.5,
  FIRST: 1.2, I0: 3.6, I_DECAY: 0.962, I_MIN: 1.25, PRACTICE_I: 3.4,
  HZ_WIN: 1.6,
  COUNTDOWN: 3, SEND_HZ: 30, DELAY: 0.12,
};
const PH = { EMPTY: 0, FEED: 1, CUT: 2, NAIL: 3, SNAP: 4, JAM: 5 };
const sawing = ph => ph === PH.CUT || ph === PH.NAIL || ph === PH.SNAP;
const ROLE_NAME = { ac: 'Wechselstrom', dc: 'Gleichstrom' };
const rolesFor = n => (n % 2 === 1 ? ['ac', 'dc'] : ['dc', 'ac']);

function rng(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6D2B79F5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
const newSeed = () => Math.floor(Math.random() * 2147483647);

/* ---------- Stämme: gleicher Startwert = gleiche Stämme für beide ---------- */
class Schedule {
  constructor(seed, practice = false, opts = {}) { this.r = rng(seed); this.logs = []; this.practice = practice; this.opts = opts; }
  get(i) { while (this.logs.length <= i) this.make(); return this.logs[i]; }
  make() {
    const i = this.logs.length, r = this.r;
    const gap = i === 0 ? CFG.FIRST : this.practice ? this.opts.interval || CFG.PRACTICE_I : Math.max(CFG.I_MIN, CFG.I0 * Math.pow(CFG.I_DECAY, i - 1));
    const t = (i ? this.logs[i - 1].t : 0) + gap;
    const D = Math.round(48 + r() * 18 + (this.practice ? 0 : Math.min(14, i * 0.6)));
    const L = Math.round(98 + r() * 24);
    const oakRoll = r(), nailRoll = r(), nailPos = r(), feedRoll = r();
    const oak = i >= 5 && oakRoll < 0.22;
    const nail = this.opts.nails !== false && i >= 3 && nailRoll < 0.25 ? 0.3 + nailPos * 0.4 : 0;
    // feed: so lange rollt der Stamm unter die Säge, jedes Mal etwas anders
    this.logs.push({ i, t, D, L, oak, nail, feed: 0.55 + feedRoll * 0.5, work: (D / 60) * (oak ? 1.4 : 1) });
  }
  spawnedBy(t) { let n = 0; while (this.get(n).t <= t) n++; return n; }
}

/* ---------- Eine Säge ---------- */
class Sawyer {
  // opts.limit: nach so vielen Sekunden ist Schluss. opts.calm: ohne Nägel und Blockieren. opts.direct: Seil folgt sofort (Erklärmodus).
  constructor(role, sched, practice, opts = {}) {
    this.role = role; this.sched = sched; this.practice = !!practice;
    this.limit = opts.limit || 0; this.calm = !!opts.calm; this.direct = !!opts.direct; this.over = false;
    this.t = 0; this.acc = 0; this.p = 0; this.v = 0; this.q = 0; this.last = 0;
    this.presses = []; this.hz = 0; this.maxHz = 0;
    this.queue = []; this.next = 0; this.k = -1; this.ph = PH.EMPTY; this.pt = 0; this.g = 0; this.nailDone = false;
    this.f = 0; this.feedMove = 0; this.jamP = 0;
    this.w = 0; this.cap = CFG.BURST; this.nailMove = 0; this.mdir = 0; this.turn = 0;
    this.c = 0; this.x = 0; this.alive = true;
  }
  // dir: -1 = nach links, +1 = nach rechts
  press(dir) {
    if (!this.alive) return 'dead';
    if (this.ph === PH.SNAP) return 'snap';
    const q0 = this.q;
    if (this.role === 'ac') {
      if (dir === this.last) return 'wrong';
      this.last = dir; this.q = dir * CFG.STROKE / 2;
      this.presses.push(this.t);
    } else {
      if (dir < 0) return 'wrong';
      this.q += CFG.STROKE;
    }
    return this.pulled(Math.abs(this.q - q0));
  }
  // Maus: Wechselstrom schiebt das Seil hin und her, höchstens bis zum Anschlag. Gleichstrom dreht es mit dem Rad weiter.
  move(d) {
    if (!this.alive) return 'dead';
    if (this.ph === PH.SNAP) return 'snap';
    const q0 = this.q;
    if (this.role === 'ac') {
      this.q = clamp(q0 + d, -CFG.STROKE / 2, CFG.STROKE / 2);
      const dir = Math.sign(d);
      if (dir && dir !== this.mdir) {
        const pr = this.presses;
        if (Math.abs(q0 - this.turn) >= 0.5 && (!pr.length || this.t - pr[pr.length - 1] >= 0.03)) pr.push(this.t);
        this.turn = q0; this.mdir = dir;
      }
    } else {
      this.q = Math.max(q0, Math.min(q0 + Math.abs(d), this.p + CFG.LEAD));
    }
    return this.pulled(Math.abs(this.q - q0));
  }
  // Gezählt wird der Weg des Seils, nicht die Richtung: hin und her sägt genau so gut wie im Kreis
  pulled(dq) {
    if (this.ph === PH.CUT) { const take = Math.min(dq, this.cap); this.cap -= take; this.w += take; }
    // Wer sägt, während der Stamm noch rollt, blockiert ihn
    if (this.calm) return 'ok';
    if (this.ph === PH.FEED && this.pt > CFG.FEED_GRACE) {
      this.feedMove += dq;
      if (this.feedMove > CFG.NAIL_SLACK) { this.jamP = this.pt; this.ph = PH.JAM; this.pt = 0; return 'jam'; }
    }
    if (this.ph === PH.NAIL && this.pt > CFG.NAIL_GRACE) {
      this.nailMove += dq;
      if (this.nailMove > CFG.NAIL_SLACK) { this.ph = PH.SNAP; this.pt = 0; this.v = 0; return 'snap'; }
    }
    return 'ok';
  }
  step(dt) {
    if (!this.alive) return;
    this.acc += dt;
    while (this.acc >= CFG.H && this.alive) { this.acc -= CFG.H; this.tick(CFG.H); }
    const pr = this.presses;
    while (pr.length && pr[0] < this.t - CFG.HZ_WIN) pr.shift();
    let f = 0;
    if (this.role === 'ac' && pr.length >= 3 && this.t - pr[pr.length - 1] < 0.5) f = (pr.length - 1) / Math.max(0.05, pr[pr.length - 1] - pr[0]) / 2;
    this.hz = f > 0 ? (this.hz > 0 ? lerp(this.hz, f, 1 - Math.exp(-dt / 0.15)) : f) : Math.max(0, this.hz - dt * 3);
    if (f > 0 && pr.length >= 5) this.maxHz = Math.max(this.maxHz, r1(f));
  }
  tick(h) {
    this.t += h;
    if (this.limit && this.t >= this.limit) { this.t = this.limit; this.alive = false; this.over = true; this.v = 0; return; }
    this.cap = Math.min(CFG.BURST, this.cap + CFG.MAX_RATE * h);
    const S = this.sched;
    while (S.get(this.next).t <= this.t) {
      if (this.queue.length < CFG.SLOTS) this.queue.push(this.next);
      else { this.x++; if (!this.practice && this.x >= CFG.LIVES) this.alive = false; }
      this.next++;
    }
    if (this.direct) { this.p = this.q; this.v = 0; }
    else if (this.ph !== PH.SNAP) {
      const w = CFG.OMEGA;
      this.v += (w * w * (this.q - this.p) - 2 * w * this.v) * h;
      // Gleichstrom läuft nie rückwärts, auch wenn das Seil über das Ziel hinausschiesst
      this.v = clamp(this.v, this.role === 'dc' ? 0 : -CFG.VMAX, CFG.VMAX);
      this.p += this.v * h;
    }
    this.pt += h;
    if (this.ph === PH.EMPTY) {
      if (this.queue.length) { this.k = this.queue.shift(); this.ph = PH.FEED; this.pt = 0; this.g = 0; this.f = 0; this.feedMove = 0; this.nailDone = false; }
    } else if (this.ph === PH.FEED) {
      const feed = S.get(this.k).feed;
      this.f = Math.min(1, this.pt / feed);
      if (this.pt >= feed) { this.ph = PH.CUT; this.pt = 0; this.f = 1; }
    } else if (this.ph === PH.JAM) {
      if (this.pt >= CFG.JAM_T) { this.ph = PH.FEED; this.pt = this.jamP; this.feedMove = 0; }
    } else if (this.ph === PH.CUT) {
      const log = S.get(this.k), d = this.w * (1 - Math.exp(-h * CFG.BITE));
      this.w -= d;
      this.g += d * CFG.CUT / log.work;
      if (log.nail && !this.nailDone && this.g >= log.nail) { this.g = log.nail; this.w = 0; this.nailMove = 0; this.ph = PH.NAIL; this.pt = 0; }
      else if (this.g >= 1) { this.g = 1; this.w = 0; this.c++; this.k = -1; this.ph = PH.EMPTY; this.pt = 0; }
    } else if (this.ph === PH.NAIL) {
      if (this.pt >= CFG.NAIL_T) { this.nailDone = true; this.ph = PH.CUT; this.pt = 0; }
    } else if (this.ph === PH.SNAP && this.pt >= CFG.REPAIR_T) {
      this.nailDone = true; this.ph = PH.CUT; this.pt = 0; this.q = this.p; this.last = 0; this.mdir = 0; this.turn = this.p;
    }
  }
}

/* ---------- Säge aus dem Netz ---------- */
class Remote {
  constructor() { this.reset(); }
  reset() { this.s = []; }
  push(s) {
    const last = this.s[this.s.length - 1];
    if (last && s.t < last.t) return;
    this.s.push(s);
    if (this.s.length > 90) this.s.shift();
  }
  get lastT() { return this.s.length ? this.s[this.s.length - 1].t : 0; }
  get latest() { return this.s[this.s.length - 1] || null; }
  sample(t) {
    const s = this.s;
    if (!s.length) return null;
    let a = s[0], b = s[0];
    if (t >= s[s.length - 1].t) a = b = s[s.length - 1];
    else if (t > s[0].t) {
      let i = s.length - 1;
      while (i > 1 && s[i - 1].t > t) i--;
      a = s[i - 1]; b = s[i];
    }
    const k = b.t > a.t ? clamp((t - a.t) / (b.t - a.t), 0, 1) : 0;
    const same = a.k === b.k && a.ph === b.ph;
    return {
      t, p: lerp(a.p, b.p, k), g: same ? lerp(a.g, b.g, k) : a.g, f: same ? lerp(a.f || 0, b.f || 0, k) : a.f || 0, ph: a.ph, pt: same ? lerp(a.pt, b.pt, k) : a.pt,
      k: a.k, q: a.q, c: a.c, x: a.x, alive: !!a.a, over: !a.a, hz: 0, maxHz: 0, practice: true,
    };
  }
}
const idleView = () => ({ t: 0, p: 0, g: 0, f: 0, ph: PH.EMPTY, pt: 0, k: -1, q: [], c: 0, x: 0, alive: true, over: false, hz: 0, maxHz: 0, practice: true });
function sawView(s) {
  return { t: s.t, p: s.p, g: s.g, f: s.f, ph: s.ph, pt: s.pt, k: s.k, q: s.queue, c: s.c, x: s.x, alive: s.alive, over: s.over, hz: s.hz, maxHz: s.maxHz, practice: s.practice };
}

/* ---------- Ton ---------- */
const Sound = {
  ctx: null, on: true, noiseBuf: null, saws: {},
  ensure() {
    if (!this.on) return null;
    if (!this.ctx) {
      const AC = window.AudioContext || window.webkitAudioContext;
      if (!AC) return null;
      try { this.ctx = new AC(); } catch (_) { return null; }
    }
    if (this.ctx.state === 'suspended') this.ctx.resume().catch(() => {});
    return this.ctx;
  },
  buf() {
    if (!this.noiseBuf) {
      const c = this.ctx, n = c.sampleRate, b = c.createBuffer(1, n, c.sampleRate), d = b.getChannelData(0);
      for (let i = 0; i < n; i++) d[i] = Math.random() * 2 - 1;
      this.noiseBuf = b;
    }
    return this.noiseBuf;
  },
  tone(f0, f1, dur, type = 'sine', vol = 0.1, delay = 0) {
    const c = this.ensure(); if (!c) return;
    const t = c.currentTime + delay;
    const o = c.createOscillator(), g = c.createGain();
    o.type = type;
    o.frequency.setValueAtTime(f0, t);
    o.frequency.exponentialRampToValueAtTime(Math.max(20, f1), t + dur);
    g.gain.setValueAtTime(0.0001, t);
    g.gain.exponentialRampToValueAtTime(vol, t + 0.01);
    g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    o.connect(g); g.connect(c.destination);
    o.start(t); o.stop(t + dur + 0.03);
  },
  noise(dur, vol, freq = 2200) {
    const c = this.ensure(); if (!c) return;
    const src = c.createBufferSource(), f = c.createBiquadFilter(), g = c.createGain(), t = c.currentTime;
    src.buffer = this.buf(); f.type = 'bandpass'; f.frequency.value = freq; f.Q.value = 0.8;
    g.gain.setValueAtTime(vol, t); g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    src.connect(f); f.connect(g); g.connect(c.destination); src.start(t, Math.random() * 0.5); src.stop(t + dur + 0.02);
  },
  // Sägegeräusch: lauter und höher, je schneller das Seil läuft
  saw(id, speed) {
    const c = this.ctx; if (!c) return;
    const level = this.on ? Math.min(1, speed / 10) * 0.08 : 0;
    let s = this.saws[id];
    if (!s) {
      if (level <= 0) return;
      const src = c.createBufferSource(), f = c.createBiquadFilter(), g = c.createGain();
      src.buffer = this.buf(); src.loop = true; f.type = 'bandpass'; f.Q.value = 1.6; g.gain.value = 0;
      src.connect(f); f.connect(g); g.connect(c.destination); src.start();
      s = this.saws[id] = { f, g };
    }
    s.g.gain.setTargetAtTime(level, c.currentTime, 0.025);
    s.f.frequency.setTargetAtTime(450 + speed * 90, c.currentTime, 0.03);
  },
  silence() { for (const id in this.saws) this.saw(id, 0); },
  beep(hi) { this.tone(hi ? 880 : 520, hi ? 880 : 520, hi ? 0.32 : 0.12, 'square', 0.04); },
  cut() { this.noise(0.2, 0.3, 900); this.tone(240, 90, 0.2, 'triangle', 0.14); },
  miss() { this.tone(170, 120, 0.4, 'square', 0.05); this.noise(0.35, 0.25, 400); },
  alarm() { this.tone(988, 988, 0.13, 'square', 0.05); this.tone(740, 740, 0.13, 'square', 0.05, 0.16); },
  snap() { this.tone(720, 60, 0.5, 'sawtooth', 0.08); this.noise(0.25, 0.35, 3000); },
  resume() { this.tone(660, 990, 0.14, 'triangle', 0.09); },
  jam() { this.tone(150, 95, 0.35, 'square', 0.07); this.noise(0.2, 0.25, 600); },
  clamp() { this.tone(1400, 1000, 0.05, 'square', 0.05); },
  wrong() { this.tone(190, 170, 0.07, 'square', 0.03); },
  win() { [523, 659, 784, 1047].forEach((f, i) => this.tone(f, f, 0.2, 'triangle', 0.1, i * 0.11)); },
  lose() { [392, 330, 262].forEach((f, i) => this.tone(f, f * 0.97, 0.22, 'triangle', 0.08, i * 0.15)); },
};
try { if (localStorage.getItem('saegewerk.sound') === '0') Sound.on = false; } catch (_) {}

/* ---------- Farben aus den CSS-Tokens ---------- */
const root = document.documentElement;
let themeTick = 0;
const mq = matchMedia('(prefers-color-scheme: dark)');
if (mq.addEventListener) mq.addEventListener('change', () => themeTick++); else if (mq.addListener) mq.addListener(() => themeTick++);
new MutationObserver(() => themeTick++).observe(root, { attributes: true, attributeFilter: ['data-theme', 'class', 'style'] });
if (document.fonts) document.fonts.ready.then(() => themeTick++);
const TOKENS = {
  hall: '--hall', hallLine: '--hall-line', belt: '--belt', beltHi: '--belt-hi', bark: '--bark', face: '--wood-face', ring: '--wood-ring',
  oakFace: '--oak-face', oakRing: '--oak-ring', crate: '--crate', steel: '--steel', rope: '--rope', ropeHi: '--rope-hi', nail: '--nail',
  copper: '--copper', copperHi: '--copper-hi', electron: '--electron', mark: '--mark', lamp: '--lamp',
  dc: '--dc', ac: '--ac', onMode: '--on-mode', bad: '--bad', ok: '--ok', warn: '--warn',
  panel: '--panel', plate: '--plate', ink: '--ink', muted: '--muted', line: '--line',
  fontBody: '--font-body', fontDisplay: '--font-display', fontMono: '--font-mono',
};
let palCache = null, palTick = -1;
function palette() {
  if (palTick !== themeTick) {
    const cs = getComputedStyle(root);
    palCache = {};
    for (const k in TOKENS) palCache[k] = cs.getPropertyValue(TOKENS[k]).trim();
    palTick = themeTick;
  }
  return palCache;
}
function rgba(hex, a) {
  let h = hex.replace('#', '');
  if (h.length === 3) h = h.split('').map(c => c + c).join('');
  const n = parseInt(h, 16);
  return `rgba(${(n >> 16) & 255},${(n >> 8) & 255},${n & 255},${a})`;
}
function fit(canvas) {
  const r = canvas.getBoundingClientRect();
  if (r.width < 2 || r.height < 2) return null;
  const dpr = Math.min(window.devicePixelRatio || 1, 2);
  const w = Math.round(r.width * dpr), h = Math.round(r.height * dpr);
  if (canvas.width !== w || canvas.height !== h) { canvas.width = w; canvas.height = h; }
  const ctx = canvas.getContext('2d');
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  return { ctx, w: r.width, h: r.height };
}

/* ---------- Szene (1000 × 640) ---------- */
const VW = 1000, VH = 640;
const BELT_Y = 392, BELT_X1 = 884, SAW_X = 730;
const SLOT_X = [478, 343, 208, 73], ENTRY_X = -80;
const RX0 = 630, RX1 = 830, RY0 = 58, RT = 34, RB = 14, YB_UP = 292;
const UNIT = 62;                  // Pixel Seil (und Elektronen) pro Einheit
const STRIP_Y = 440;
const E_GAP = 36;

// Geschlossene Schlaufe, beginnt unten links. Positive Richtung: unten nach rechts, oben nach links.
function loopPath(x0, y0, x1, y1, rT, rB) {
  const segs = [];
  const L = (ax, ay, bx, by) => segs.push({ L: 1, ax, ay, bx, by, len: Math.hypot(bx - ax, by - ay) });
  const A = (cx, cy, r, a0, a1) => segs.push({ A: 1, cx, cy, r, a0, a1, len: Math.abs(a1 - a0) * r });
  L(x0 + rB, y1, x1 - rB, y1);
  A(x1 - rB, y1 - rB, rB, Math.PI / 2, 0);
  L(x1, y1 - rB, x1, y0 + rT);
  A(x1 - rT, y0 + rT, rT, 0, -Math.PI / 2);
  L(x1 - rT, y0, x0 + rT, y0);
  A(x0 + rT, y0 + rT, rT, -Math.PI / 2, -Math.PI);
  L(x0, y0 + rT, x0, y1 - rB);
  A(x0 + rB, y1 - rB, rB, -Math.PI, -Math.PI * 1.5);
  let total = 0;
  for (const s of segs) { s.s0 = total; total += s.len; }
  const top = segs[4];
  return { segs, total, topMid: top.s0 + top.len / 2 };
}
function pathAt(P, s) {
  s = ((s % P.total) + P.total) % P.total;
  for (const g of P.segs) {
    if (s <= g.s0 + g.len) {
      const k = (s - g.s0) / (g.len || 1);
      if (g.L) return { x: lerp(g.ax, g.bx, k), y: lerp(g.ay, g.by, k) };
      const a = lerp(g.a0, g.a1, k);
      return { x: g.cx + g.r * Math.cos(a), y: g.cy + g.r * Math.sin(a) };
    }
  }
  return { x: P.segs[0].ax, y: P.segs[0].ay };
}
function tracePath(ctx, P, from = 0, to = P.segs.length) {
  ctx.beginPath();
  for (let i = from; i < to; i++) {
    const g = P.segs[i];
    if (g.L) { if (i === from) ctx.moveTo(g.ax, g.ay); ctx.lineTo(g.bx, g.by); }
    else { if (i === from) ctx.moveTo(g.cx + g.r * Math.cos(g.a0), g.cy + g.r * Math.sin(g.a0)); ctx.arc(g.cx, g.cy, g.r, g.a0, g.a1, true); }
  }
}
const E_PATH = loopPath(84, 486, 930, 592, 22, 22);

function roundRect(ctx, x, y, w, h, r) {
  ctx.beginPath();
  ctx.moveTo(x + r, y);
  ctx.arcTo(x + w, y, x + w, y + h, r); ctx.arcTo(x + w, y + h, x, y + h, r);
  ctx.arcTo(x, y + h, x, y, r); ctx.arcTo(x, y, x + w, y, r);
  ctx.closePath();
}
function drawSym(ctx, type, cx, cy, size, color, lw) {
  const hw = size / 2;
  ctx.strokeStyle = color; ctx.lineWidth = lw; ctx.lineCap = 'butt';
  ctx.beginPath();
  if (type === 'dc') {
    const gap = size * 0.17, dl = size * 0.22, gp = (size - 3 * dl) / 2;
    ctx.moveTo(cx - hw, cy - gap); ctx.lineTo(cx + hw, cy - gap);
    for (let i = 0; i < 3; i++) { const x = cx - hw + i * (dl + gp); ctx.moveTo(x, cy + gap); ctx.lineTo(x + dl, cy + gap); }
  } else {
    const a = size * 0.26;
    for (let i = 0; i <= 32; i++) {
      const t = i / 32, x = cx - hw + t * size, y = cy - Math.sin(t * TAU) * a;
      if (i) ctx.lineTo(x, y); else ctx.moveTo(x, y);
    }
  }
  ctx.stroke();
}
function pill(ctx, x, y, text, font, color, bg, border) {
  ctx.font = font;
  const tw = ctx.measureText(text).width, h = parseInt(font.match(/(\d+)px/)[1], 10) * 1.5;
  roundRect(ctx, x - tw / 2 - 20, y - h / 2, tw + 40, h, 12);
  ctx.fillStyle = bg; ctx.fill();
  if (border) { ctx.strokeStyle = border; ctx.lineWidth = 3; ctx.stroke(); }
  ctx.fillStyle = color; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  ctx.fillText(text, x, y + 2);
}

// Stamm von der Seite, Stirnseite rechts. by = Unterkante.
function drawLog(ctx, P, cx, by, L, D, oak, o = {}) {
  const top = by - D, x0 = cx - L / 2, x1 = cx + L / 2, ex = Math.max(5, D * 0.16), mid = top + D / 2;
  ctx.beginPath();
  ctx.moveTo(x1, top); ctx.lineTo(x0 + ex, top);
  ctx.ellipse(x0 + ex, mid, ex, D / 2, 0, -Math.PI / 2, Math.PI / 2, true);
  ctx.lineTo(x1, by); ctx.closePath();
  ctx.fillStyle = P.bark; ctx.fill();
  ctx.strokeStyle = 'rgba(0,0,0,0.25)'; ctx.lineWidth = 2;
  ctx.beginPath();
  for (const k of [0.27, 0.55, 0.8]) {
    const y = top + D * k;
    ctx.moveTo(x0 + ex * 1.3, y); ctx.bezierCurveTo(x0 + L * 0.35, y - 3, x0 + L * 0.65, y + 3, x1 - 3, y);
  }
  ctx.stroke();
  ctx.beginPath(); ctx.ellipse(x1, mid, ex, D / 2, 0, 0, TAU);
  ctx.fillStyle = oak ? P.oakFace : P.face; ctx.fill();
  ctx.strokeStyle = P.bark; ctx.lineWidth = 3; ctx.stroke();
  ctx.strokeStyle = oak ? P.oakRing : P.ring; ctx.lineWidth = 1.5;
  for (const k of [0.7, 0.42, 0.16]) { ctx.beginPath(); ctx.ellipse(x1, mid, ex * k, (D / 2) * k, 0, 0, TAU); ctx.stroke(); }
  if (oak && L > 70) {
    ctx.font = `800 14px ${P.fontDisplay}`; ctx.fillStyle = rgba(P.oakFace, 0.95); ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.fillText('EICHE', cx - (o.g ? 30 : 0), mid + 1);
  }
  if (o.g > 0) { ctx.fillStyle = P.belt; ctx.fillRect(cx - 3, top - 1, 6, o.g * D + 1); }
  if (o.nail) {
    const ny = top + o.nail * D;
    ctx.beginPath(); ctx.arc(cx, ny, 6, 0, TAU);
    ctx.fillStyle = P.nail; ctx.fill(); ctx.strokeStyle = P.ink; ctx.lineWidth = 2; ctx.stroke();
    ctx.beginPath(); ctx.arc(cx - 2, ny - 2, 1.8, 0, TAU); ctx.fillStyle = '#ffffff'; ctx.fill();
  }
}
function drawPiece(ctx, P, pc) {
  ctx.save();
  ctx.translate(pc.x, pc.y - pc.D / 2);
  ctx.rotate(pc.rot);
  drawLog(ctx, P, 0, pc.D / 2, pc.L, pc.D, pc.oak);
  ctx.restore();
}
function drawWheel(ctx, P, x, y, r, rot, hub, crank) {
  ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
  ctx.beginPath(); ctx.arc(0, 0, r - 3, 0, TAU);
  ctx.fillStyle = P.panel; ctx.fill(); ctx.lineWidth = 4; ctx.strokeStyle = P.steel; ctx.stroke();
  ctx.lineWidth = 3; ctx.beginPath();
  const n = r < 20 ? 1 : 4; // kleine Rollen mit nur einer Speiche, sonst flimmern sie rückwärts
  for (let i = 0; i < n; i++) { const a = (i * TAU) / n; ctx.moveTo(0, 0); ctx.lineTo(Math.cos(a) * (r - 5), Math.sin(a) * (r - 5)); }
  ctx.stroke();
  ctx.beginPath(); ctx.arc(0, 0, Math.max(4, r * 0.24), 0, TAU); ctx.fillStyle = hub || P.steel; ctx.fill();
  if (crank) {
    ctx.beginPath(); ctx.arc(r * 0.62, 0, 7, 0, TAU); ctx.fillStyle = hub; ctx.fill();
    ctx.strokeStyle = P.ink; ctx.lineWidth = 2; ctx.stroke();
  }
  ctx.restore();
}
function drawMagnet(ctx, P, x, y) {
  ctx.save(); ctx.translate(x, y);
  ctx.strokeStyle = P.steel; ctx.lineWidth = 3; ctx.beginPath(); ctx.moveTo(0, -24); ctx.lineTo(0, -400); ctx.stroke();
  ctx.lineCap = 'butt'; ctx.lineWidth = 12; ctx.strokeStyle = P.bad;
  ctx.beginPath(); ctx.arc(0, -8, 14, Math.PI, 0); ctx.lineTo(14, 10); ctx.moveTo(-14, -8); ctx.lineTo(-14, 10); ctx.stroke();
  ctx.strokeStyle = P.nail; ctx.beginPath(); ctx.moveTo(-14, 10); ctx.lineTo(-14, 18); ctx.moveTo(14, 10); ctx.lineTo(14, 18); ctx.stroke();
  ctx.restore();
}

function drawHall(ctx, P, fx, view) {
  ctx.fillStyle = P.hall; ctx.fillRect(0, 0, VW, STRIP_Y);
  ctx.strokeStyle = P.hallLine; ctx.lineWidth = 2; ctx.beginPath();
  for (let x = 40; x < VW; x += 120) { ctx.moveTo(x, 0); ctx.lineTo(x, BELT_Y); }
  ctx.stroke();
  ctx.fillStyle = P.steel; ctx.fillRect(600, 0, 260, 14);
  // Rollen und Band
  const y = BELT_Y;
  for (let x = 22; x <= BELT_X1 - 8; x += 60) {
    ctx.save(); ctx.translate(x, y + 22); ctx.rotate(fx.beltOff / 9);
    ctx.beginPath(); ctx.arc(0, 0, 9, 0, TAU); ctx.fillStyle = P.beltHi; ctx.fill();
    ctx.strokeStyle = P.belt; ctx.lineWidth = 2.5; ctx.beginPath(); ctx.moveTo(-6, 0); ctx.lineTo(6, 0); ctx.stroke();
    ctx.restore();
  }
  roundRect(ctx, 0, y, BELT_X1, 14, 7); ctx.fillStyle = P.belt; ctx.fill();
  ctx.save(); roundRect(ctx, 0, y, BELT_X1, 14, 7); ctx.clip();
  ctx.strokeStyle = P.beltHi; ctx.lineWidth = 2; ctx.beginPath();
  for (let x = -(fx.beltOff % 30); x < BELT_X1; x += 30) { ctx.moveTo(x, y + 3); ctx.lineTo(x + 7, y + 11); }
  ctx.stroke(); ctx.restore();
  // Band voll: Warnung links
  if (view.q.length >= CFG.SLOTS && Math.sin(performance.now() / 110) > -0.3) {
    pill(ctx, 150, 285, 'BAND VOLL!', `800 24px ${P.fontDisplay}`, '#ffffff', P.bad);
  }
}

function drawCrate(ctx, P, view) {
  roundRect(ctx, 892, 402, 104, 36, 5); ctx.fillStyle = P.crate; ctx.fill();
  ctx.strokeStyle = 'rgba(0,0,0,0.3)'; ctx.lineWidth = 2; ctx.stroke();
  ctx.font = `800 24px ${P.fontDisplay}`; ctx.fillStyle = '#ffffff'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  ctx.fillText(String(view.c), 944, 421);
}

function drawRope(ctx, P, view, fx, rp) {
  const off = view.p * UNIT;
  const snapped = view.ph === PH.SNAP;
  // Gestänge, an dem die unteren Rollen hängen
  ctx.strokeStyle = P.steel; ctx.lineWidth = 4; ctx.beginPath();
  ctx.moveTo(RX0 + RB, 14); ctx.lineTo(RX0 + RB, fx.yB - RB);
  ctx.moveTo(RX1 - RB, 14); ctx.lineTo(RX1 - RB, fx.yB - RB);
  ctx.stroke();
  ctx.lineCap = 'round'; ctx.lineJoin = 'round';
  if (snapped) tracePath(ctx, rp, 1, rp.segs.length); else { tracePath(ctx, rp); ctx.closePath(); }
  ctx.strokeStyle = P.rope; ctx.lineWidth = 7; ctx.stroke();
  ctx.setLineDash([20, 20]);
  ctx.lineDashOffset = -(((off - rp.topMid) % 40) + 40) % 40;
  ctx.strokeStyle = rgba(P.ropeHi, clamp(1 - fx.speed / 16, 0.2, 0.9)); ctx.lineWidth = 3; ctx.stroke();
  ctx.setLineDash([]);
  if (snapped) {
    // lose Enden
    const yb = fx.yB, sway = Math.sin(performance.now() / 160) * 6;
    ctx.strokeStyle = P.rope; ctx.lineWidth = 7; ctx.beginPath();
    ctx.moveTo(RX0 + RB, yb); ctx.quadraticCurveTo(RX0 + 34, yb + 10, RX0 + 26 + sway, yb + 38);
    ctx.moveTo(RX1 - RB, yb); ctx.quadraticCurveTo(RX1 - 34, yb + 10, RX1 - 26 - sway, yb + 38);
    ctx.stroke();
  }
}
// Zu schnell fürs Auge: der Punkt erscheint als Streifen zwischen den Umkehrpunkten
function smear(ctx, path, s, amp, r, color) {
  ctx.fillStyle = color; ctx.globalAlpha = 0.16; ctx.beginPath();
  for (let i = 0; i <= 14; i++) { const pt = pathAt(path, s - amp + (2 * amp * i) / 14); ctx.moveTo(pt.x + r, pt.y); ctx.arc(pt.x, pt.y, r, 0, TAU); }
  ctx.fill(); ctx.globalAlpha = 1;
}
function drawRopeFront(ctx, P, view, fx, rp, role, o) {
  const off = view.p * UNIT, rot = -off;
  const col = role === 'ac' ? P.ac : P.dc;
  const top = RY0 + fx.yB - YB_UP + RT;
  drawWheel(ctx, P, RX0 + RT, top, RT, rot / RT, col, true);
  drawWheel(ctx, P, RX1 - RT, top, RT, rot / RT, null, false);
  drawWheel(ctx, P, RX0 + RB, fx.yB - RB, RB, rot / RB, null, false);
  drawWheel(ctx, P, RX1 - RB, fx.yB - RB, RB, rot / RB, null, false);
  // gelber Punkt am Seil
  if (view.ph !== PH.SNAP && o.blur) smear(ctx, rp, rp.topMid + off, o.blur * UNIT, 9, P.mark);
  else if (view.ph !== PH.SNAP) {
    const m = pathAt(rp, rp.topMid + off);
    ctx.beginPath(); ctx.arc(m.x, m.y, 9, 0, TAU);
    ctx.fillStyle = P.mark; ctx.fill(); ctx.strokeStyle = P.ink; ctx.lineWidth = 2.5; ctx.stroke();
  }
}

function drawStation(ctx, P, view, sched, fx) {
  if (view.k < 0) return;
  const log = sched.get(view.k), L = fx.logs.get(view.k);
  const jam = view.ph === PH.JAM;
  const x = (L ? L.x : SAW_X) + (jam ? Math.sin(performance.now() / 22) * 3 : 0);
  const cutting = sawing(view.ph);
  const nailIn = log.nail && (view.g < log.nail - 0.004 || ((view.ph === PH.NAIL || view.ph === PH.SNAP) && view.pt < CFG.LIFT));
  drawLog(ctx, P, x, BELT_Y, log.L, log.D, log.oak, { g: cutting ? view.g : 0, nail: nailIn ? log.nail : 0 });
  // Seil im Schnitt
  if (cutting && view.ph !== PH.SNAP) {
    ctx.strokeStyle = P.rope; ctx.lineWidth = 6; ctx.lineCap = 'round';
    ctx.beginPath(); ctx.moveTo(x - 3, fx.yB); ctx.lineTo(x + 3, fx.yB); ctx.stroke();
  }
  if (view.ph === PH.FEED && view.alive) pill(ctx, x, BELT_Y - log.D - 26, 'Warten …', `700 18px ${P.fontDisplay}`, P.ink, rgba(P.panel, 0.92), P.line);
  // Magnet holt den Nagel
  if (log.nail && (view.ph === PH.NAIL || view.ph === PH.SNAP) && view.pt < CFG.NAIL_T) {
    const ny = BELT_Y - log.D + log.nail * log.D, pt = view.pt;
    let my;
    if (pt < 0.45) my = lerp(-60, ny - 30, pt / 0.45);
    else if (pt < CFG.LIFT) my = ny - 30;
    else my = lerp(ny - 30, -60, (pt - CFG.LIFT) / (CFG.NAIL_T - CFG.LIFT));
    if (pt >= CFG.LIFT) {
      ctx.beginPath(); ctx.arc(x, my + 30, 6, 0, TAU); ctx.fillStyle = P.nail; ctx.fill();
      ctx.strokeStyle = P.ink; ctx.lineWidth = 2; ctx.stroke();
      ctx.strokeStyle = P.nail; ctx.lineWidth = 3; ctx.beginPath(); ctx.moveTo(x, my + 36); ctx.lineTo(x, my + 58); ctx.stroke();
    }
    drawMagnet(ctx, P, x, my);
  }
  // Vorwarnung
  if (log.nail && view.ph === PH.CUT && view.g < log.nail && view.g > log.nail - 0.18 && Math.sin(performance.now() / 90) > -0.2) {
    pill(ctx, x, BELT_Y - log.D - 26, 'Achtung, Nagel!', `800 20px ${P.fontDisplay}`, P.ink, P.warn);
  }
}

// Ampel an der Säge: Grün heisst sägen, Rot heisst warten
function drawSignal(ctx, P, view) {
  const x = 880, y = 168, red = view.ph === PH.FEED || view.ph === PH.JAM || view.ph === PH.NAIL || view.ph === PH.SNAP, green = view.ph === PH.CUT;
  ctx.strokeStyle = P.steel; ctx.lineWidth = 4; ctx.beginPath(); ctx.moveTo(856, 7); ctx.lineTo(x, 7); ctx.lineTo(x, y - 40); ctx.stroke();
  roundRect(ctx, x - 20, y - 40, 40, 80, 10); ctx.fillStyle = P.belt; ctx.fill();
  const lamp = (cy, on, col) => {
    if (on) { const g = ctx.createRadialGradient(x, cy, 4, x, cy, 34); g.addColorStop(0, rgba(col, 0.6)); g.addColorStop(1, rgba(col, 0)); ctx.fillStyle = g; ctx.beginPath(); ctx.arc(x, cy, 34, 0, TAU); ctx.fill(); }
    ctx.beginPath(); ctx.arc(x, cy, 13, 0, TAU); ctx.fillStyle = on ? col : rgba(col, 0.22); ctx.fill();
  };
  lamp(y - 18, red, P.bad);
  lamp(y + 18, green, P.ok);
}

function drawHud(ctx, P, view, o) {
  const col = o.role === 'ac' ? P.ac : P.dc;
  const label = ROLE_NAME[o.role].toUpperCase();
  ctx.font = `800 26px ${P.fontDisplay}`;
  const tw = ctx.measureText(label).width;
  roundRect(ctx, 16, 14, tw + 66, 42, 9); ctx.fillStyle = col; ctx.fill();
  drawSym(ctx, o.role, 39, 35, 28, P.onMode, 3.5);
  ctx.fillStyle = P.onMode; ctx.textAlign = 'left'; ctx.textBaseline = 'middle';
  ctx.fillText(label, 62, 36);
  ctx.textBaseline = 'alphabetic';
  if (o.showHz) {
    ctx.font = `700 40px ${P.fontMono}`; ctx.fillStyle = col;
    ctx.fillText(o.role === 'ac' ? fmtHz(o.hz) : '0 Hz', 16, 104);
    ctx.font = `600 17px ${P.fontBody}`; ctx.fillStyle = P.muted;
    ctx.fillText(o.role === 'ac' ? 'so oft pro Sekunde hin und her' : 'nie umgekehrt: immer vorwärts', 16, 129);
  } else {
    ctx.font = `600 19px ${P.fontBody}`; ctx.fillStyle = P.muted;
    ctx.fillText(o.role === 'ac' ? 'Seil fährt hin und her' : 'Seil läuft immer vorwärts', 16, 84);
  }
  ctx.textAlign = 'right';
  ctx.font = `700 15px ${P.fontBody}`; ctx.fillStyle = P.muted; ctx.fillText('STÄMME', 984, 30);
  ctx.font = `800 56px ${P.fontDisplay}`; ctx.fillStyle = P.ink; ctx.fillText(String(view.c), 984, 84);
}

// Maus als Anleitung: bei Wechselstrom fährt sie mit dem Seil hin und her, bei Gleichstrom dreht das Rad
function drawMouse(ctx, P, o, fx, view) {
  const ac = o.role === 'ac', col = ac ? P.ac : P.dc, cy = 92;
  const cx = 470 + (ac ? clamp(view.p, -1.2, 1.2) * 26 : 0), moving = fx.speed > 0.8;
  ctx.strokeStyle = col; ctx.lineWidth = 3; ctx.lineCap = 'round'; ctx.lineJoin = 'round';
  if (ac) {
    for (const s of [-1, 1]) {
      const x = 470 + s * 72;
      ctx.globalAlpha = moving && fx.dir === s ? 1 : 0.3;
      ctx.beginPath(); ctx.moveTo(x - s * 14, cy); ctx.lineTo(x + s * 8, cy);
      ctx.moveTo(x - s * 1, cy - 10); ctx.lineTo(x + s * 9, cy); ctx.lineTo(x - s * 1, cy + 10); ctx.stroke();
    }
    ctx.globalAlpha = 1;
  }
  roundRect(ctx, cx - 21, cy - 32, 42, 64, 21); ctx.fillStyle = P.panel; ctx.fill(); ctx.stroke();
  ctx.beginPath(); ctx.moveTo(cx - 21, cy - 6); ctx.lineTo(cx + 21, cy - 6); ctx.moveTo(cx, cy - 32); ctx.lineTo(cx, cy - 6); ctx.stroke();
  roundRect(ctx, cx - 5, cy - 27, 10, 17, 5); ctx.fillStyle = ac ? P.panel : col; ctx.fill(); ctx.stroke();
  if (!ac) {
    ctx.save(); roundRect(ctx, cx - 5, cy - 27, 10, 17, 5); ctx.clip();
    ctx.strokeStyle = P.onMode; ctx.lineWidth = 2; ctx.beginPath();
    const off = (((view.p * 12) % 5) + 5) % 5;
    for (let y = cy - 32 + off; y < cy - 8; y += 5) { ctx.moveTo(cx - 5, y); ctx.lineTo(cx + 5, y); }
    ctx.stroke(); ctx.restore();
    ctx.globalAlpha = moving ? 1 : 0.3;
    const ax0 = cx + 46, ay0 = cy - 12, r = 14, a = Math.PI * 0.6;
    ctx.beginPath(); ctx.arc(ax0, ay0, r, -Math.PI * 0.8, a); ctx.stroke();
    const ax = ax0 + r * Math.cos(a), ay = ay0 + r * Math.sin(a), tx = -Math.sin(a), ty = Math.cos(a);
    ctx.beginPath(); ctx.moveTo(ax - tx * 9 - ty * 6, ay - ty * 9 + tx * 6); ctx.lineTo(ax, ay); ctx.lineTo(ax - tx * 9 + ty * 6, ay - ty * 9 - tx * 6); ctx.stroke();
    ctx.globalAlpha = 1;
  }
  ctx.font = `600 16px ${P.fontBody}`; ctx.fillStyle = P.muted; ctx.textAlign = 'center'; ctx.textBaseline = 'alphabetic';
  ctx.fillText(ac ? 'Maus hin und her' : 'Mausrad drehen', 470, cy + 54);
}

function drawCircuit(ctx, P, view, fx, o) {
  const off = view.p * UNIT;
  ctx.fillStyle = P.panel; ctx.fillRect(0, STRIP_Y, VW, VH - STRIP_Y);
  ctx.fillStyle = P.line; ctx.fillRect(0, STRIP_Y, VW, 2);
  // Richtung der Elektronen
  let txt;
  if (!view.alive || view.ph === PH.SNAP || fx.speed < 0.4) txt = 'Elektronen: stehen still';
  else if (o.role === 'ac') txt = o.showHz ? `Elektronen: hin und her · ${fmtHz(o.hz)}` : 'Elektronen: hin und her';
  else txt = 'Elektronen: fliessen im Kreis  →';
  ctx.font = `700 17px ${P.fontMono}`; ctx.fillStyle = P.ink; ctx.textAlign = 'left'; ctx.textBaseline = 'alphabetic';
  ctx.fillText(txt, 170, 472);
  ctx.font = `700 13px ${P.fontBody}`; ctx.fillStyle = P.muted; ctx.textAlign = 'right';
  ctx.fillText('IM STROMKREIS', 984, 472);
  // Draht
  ctx.lineJoin = 'round';
  tracePath(ctx, E_PATH); ctx.closePath();
  ctx.strokeStyle = P.copper; ctx.lineWidth = 16; ctx.stroke();
  ctx.strokeStyle = P.copperHi; ctx.lineWidth = 7; ctx.stroke();
  // Elektronen bewegen sich genau wie das Seil
  const n = Math.floor(E_PATH.total / E_GAP), gap = E_PATH.total / n;
  if (o.blur) {
    for (let i = 0; i < n; i++) smear(ctx, E_PATH, E_PATH.topMid + off + (i + 0.5) * gap, o.blur * UNIT, 4.5, P.electron);
    smear(ctx, E_PATH, E_PATH.topMid + off, o.blur * UNIT, 7.5, P.mark);
  } else {
    ctx.fillStyle = P.electron; ctx.beginPath();
    for (let i = 0; i < n; i++) {
      const pt = pathAt(E_PATH, E_PATH.topMid + off + (i + 0.5) * gap);
      ctx.moveTo(pt.x + 4.5, pt.y); ctx.arc(pt.x, pt.y, 4.5, 0, TAU);
    }
    ctx.fill();
    const m = pathAt(E_PATH, E_PATH.topMid + off);
    ctx.beginPath(); ctx.arc(m.x, m.y, 7.5, 0, TAU);
    ctx.fillStyle = P.mark; ctx.fill(); ctx.strokeStyle = P.electron; ctx.lineWidth = 2; ctx.stroke();
  }
  // Quelle
  const col = o.role === 'ac' ? P.ac : P.dc;
  roundRect(ctx, 16, 470, 132, 138, 10); ctx.fillStyle = P.panel; ctx.fill(); ctx.strokeStyle = P.ink; ctx.lineWidth = 2.5; ctx.stroke();
  ctx.save(); roundRect(ctx, 16, 470, 132, 138, 10); ctx.clip(); ctx.fillStyle = col; ctx.fillRect(16, 470, 132, 30); ctx.restore();
  drawSym(ctx, o.role, 82, 485, 30, P.onMode, 3.5);
  ctx.fillStyle = P.ink; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  ctx.font = `800 28px ${P.fontDisplay}`; ctx.fillText(o.who, 82, 538);
  ctx.font = `600 14px ${P.fontBody}`; ctx.fillStyle = P.muted; ctx.fillText('Stromquelle', 82, 568);
  ctx.fillText('= Antrieb', 82, 586);
  // Lampe
  const lx = 930, ly = 539, b = fx.lamp;
  if (b > 0.02) {
    const rad = 30 + 60 * b, g = ctx.createRadialGradient(lx, ly, 10, lx, ly, rad);
    g.addColorStop(0, rgba(P.lamp, 0.85 * b)); g.addColorStop(1, rgba(P.lamp, 0));
    ctx.fillStyle = g; ctx.beginPath(); ctx.arc(lx, ly, rad, 0, TAU); ctx.fill();
  }
  ctx.beginPath(); ctx.arc(lx, ly, 26, 0, TAU);
  ctx.fillStyle = P.panel; ctx.fill();
  if (b > 0.01) { ctx.globalAlpha = b; ctx.fillStyle = P.lamp; ctx.fill(); ctx.globalAlpha = 1; }
  ctx.strokeStyle = P.ink; ctx.lineWidth = 3; ctx.stroke();
  ctx.beginPath(); ctx.moveTo(lx - 18, ly - 18); ctx.lineTo(lx + 18, ly + 18); ctx.moveTo(lx + 18, ly - 18); ctx.lineTo(lx - 18, ly + 18); ctx.stroke();
  ctx.font = `600 14px ${P.fontBody}`; ctx.fillStyle = P.muted; ctx.textAlign = 'right'; ctx.textBaseline = 'middle';
  ctx.fillText('Lampe = Holz', 892, 618);
}

function drawScene(c, view, sched, fx, o) {
  const P = palette(), { ctx, w, h } = c;
  const s = Math.min(w / VW, h / VH);
  ctx.clearRect(0, 0, w, h);
  ctx.save();
  ctx.translate((w - VW * s) / 2, (h - VH * s) / 2);
  ctx.scale(s, s);
  ctx.beginPath(); ctx.rect(0, 0, VW, VH); ctx.clip();
  ctx.save();
  if (fx.shake > 0) ctx.translate((Math.random() - 0.5) * 30 * fx.shake, (Math.random() - 0.5) * 30 * fx.shake);
  ctx.beginPath(); ctx.rect(0, 0, VW, STRIP_Y); ctx.clip();
  drawHall(ctx, P, fx, view);
  // wartende Stämme
  view.q.forEach(i => {
    const L = fx.logs.get(i); if (!L) return;
    const log = sched.get(i);
    drawLog(ctx, P, L.x, BELT_Y, log.L, log.D, log.oak, { nail: log.nail });
  });
  // Die ganze Säge senkt sich. Das Seil wird dabei nicht länger, sonst würde der gelbe Punkt verrutschen.
  const rp = loopPath(RX0, RY0 + fx.yB - YB_UP, RX1, fx.yB, RT, RB);
  drawRope(ctx, P, view, fx, rp);
  drawStation(ctx, P, view, sched, fx);
  drawRopeFront(ctx, P, view, fx, rp, o.role, o);
  drawSignal(ctx, P, view);
  for (const d of fx.dust) {
    ctx.globalAlpha = clamp(d.life / 0.4, 0, 1); ctx.fillStyle = P.face;
    ctx.fillRect(d.x - d.r, d.y - d.r, d.r * 2, d.r * 2);
  }
  ctx.globalAlpha = 1;
  for (const pc of fx.pieces) drawPiece(ctx, P, pc);
  for (const pc of fx.lost) drawPiece(ctx, P, pc);
  drawCrate(ctx, P, view);
  if (fx.xflash > 0) {
    ctx.globalAlpha = clamp(fx.xflash / 0.3, 0, 1);
    ctx.strokeStyle = P.bad; ctx.lineWidth = 12; ctx.lineCap = 'round';
    ctx.beginPath(); ctx.moveTo(14, 300); ctx.lineTo(74, 360); ctx.moveTo(74, 300); ctx.lineTo(14, 360); ctx.stroke();
    ctx.globalAlpha = 1;
  }
  drawHud(ctx, P, view, o);
  if (o.mouse && view.alive) drawMouse(ctx, P, o, fx, view);
  if (o.tag) pill(ctx, 470, 172, o.tag, `700 16px ${P.fontMono}`, P.muted, rgba(P.panel, 0.9));
  // Meldungen
  if (view.ph === PH.NAIL && view.alive) {
    if (Math.sin(performance.now() / 70) > -0.4) pill(ctx, 420, 236, 'STOPP! NAGEL!', `800 44px ${P.fontDisplay}`, '#ffffff', P.bad);
  } else if (view.ph === PH.JAM && view.alive) {
    pill(ctx, 420, 220, 'BLOCKIERT!', `800 40px ${P.fontDisplay}`, '#ffffff', P.bad);
    pill(ctx, 420, 270, 'Zu früh gesägt. Erst bei Grün!', `700 20px ${P.fontBody}`, P.ink, P.warn);
  } else if (view.ph === PH.SNAP && view.alive) {
    pill(ctx, 420, 220, 'SEIL GERISSEN!', `800 40px ${P.fontDisplay}`, '#ffffff', P.bad);
    roundRect(ctx, 290, 256, 260, 22, 11); ctx.fillStyle = rgba(P.panel, 0.95); ctx.fill(); ctx.strokeStyle = P.ink; ctx.lineWidth = 2; ctx.stroke();
    roundRect(ctx, 293, 259, 254 * clamp(view.pt / CFG.REPAIR_T, 0, 1), 16, 8); ctx.fillStyle = P.ok; ctx.fill();
    ctx.font = `600 15px ${P.fontBody}`; ctx.fillStyle = P.ink; ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.fillText('Flicken …', 420, 292);
  } else if (fx.banner && fx.banner.age < fx.banner.dur) {
    const b = fx.banner;
    ctx.globalAlpha = b.age < 0.1 ? b.age / 0.1 : b.age > b.dur - 0.3 ? (b.dur - b.age) / 0.3 : 1;
    const bg = b.kind === 'ok' ? P.ok : b.kind === 'warn' ? P.warn : P.bad;
    pill(ctx, 420, 236, b.text, `800 ${b.small ? 26 : 38}px ${P.fontDisplay}`, b.kind === 'warn' ? P.ink : '#ffffff', bg);
    ctx.globalAlpha = 1;
  }
  if (o.target && view.alive) pill(ctx, 420, 180, o.target, `800 30px ${P.fontDisplay}`, '#ffffff', P.ok);
  const st = `${view.c} ${view.c === 1 ? 'Stamm' : 'Stämme'}`;
  if (fx.win) {
    ctx.fillStyle = rgba(P.panel, fx.win === 'win' ? 0.35 : 0.72); ctx.fillRect(0, 0, VW, STRIP_Y);
    const bounce = fx.win === 'win' ? Math.abs(Math.sin(fx.winT * 5)) * 14 * Math.exp(-fx.winT * 0.6) : 0;
    const big = fx.win === 'win' ? 'SIEG!' : fx.win === 'tie' ? 'UNENTSCHIEDEN' : 'VERLOREN';
    pill(ctx, VW / 2, 170 - bounce, big, `800 ${fx.win === 'win' ? 84 : 60}px ${P.fontDisplay}`, '#ffffff', fx.win === 'win' ? P.ok : fx.win === 'tie' ? P.warn : P.muted);
    pill(ctx, VW / 2, 262, st, `700 30px ${P.fontBody}`, P.ink, P.panel, P.line);
  } else if (!view.alive) {
    ctx.fillStyle = rgba(P.panel, 0.72); ctx.fillRect(0, 0, VW, STRIP_Y);
    pill(ctx, VW / 2, 170, 'ZEIT UM!', `800 72px ${P.fontDisplay}`, '#ffffff', P.ink);
    pill(ctx, VW / 2, 252, st + ' gesägt', `700 28px ${P.fontBody}`, P.ink, P.panel, P.line);
  } else if (o.hint) {
    ctx.fillStyle = rgba(P.panel, 0.7); ctx.fillRect(0, 0, VW, STRIP_Y);
    pill(ctx, VW / 2, 180, o.hint.big, `800 50px ${P.fontDisplay}`, '#ffffff', o.role === 'ac' ? P.ac : P.dc);
    if (o.hint.small) pill(ctx, VW / 2, 252, o.hint.small, `600 22px ${P.fontBody}`, P.ink, P.panel, P.line);
  }
  for (const k of fx.confetti) {
    ctx.save(); ctx.translate(k.x, k.y); ctx.rotate(k.rot);
    ctx.fillStyle = P[k.col] || P.mark; ctx.fillRect(-k.w / 2, -3, k.w, 6);
    ctx.restore();
  }
  ctx.restore();
  drawCircuit(ctx, P, view, fx, o);
  ctx.restore();
}

/* ---------- Bewegung und Effekte pro Bildschirm ---------- */
function makeFx() {
  return { logs: new Map(), pieces: [], lost: [], dust: [], confetti: [], win: null, winT: 0, banner: null, shake: 0, xflash: 0, lamp: 0, speed: 0, dir: 1, flash: 0, yB: YB_UP, beltOff: 0, prev: null };
}
function resetFx(fx) { Object.assign(fx, makeFx()); }
function banner(fx, text, kind, dur = 1.1, small = false) { fx.banner = { text, kind, dur, small, age: 0 }; }
// Siegesfeier: Konfetti regnet über die Säge
function celebrate(fx, result) {
  fx.win = result; fx.winT = 0;
  if (result !== 'win') return;
  const cols = ['ac', 'dc', 'mark', 'ok', 'lamp'];
  for (let i = 0; i < 160; i++) {
    fx.confetti.push({ x: Math.random() * VW, y: -20 - Math.random() * 300, vx: (Math.random() - 0.5) * 120, vy: 60 + Math.random() * 120,
      rot: Math.random() * TAU, vr: (Math.random() - 0.5) * 10, w: 8 + Math.random() * 8, col: cols[i % cols.length] });
  }
}
function updateFx(fx, view, sched, dt, snd) {
  const pv = fx.prev;
  if (pv) {
    const dp = view.p - pv.p, sp = dt > 0 ? Math.abs(dp) / dt : 0;
    fx.speed += (sp - fx.speed) * (1 - Math.exp(-dt / 0.05));
    if (Math.abs(dp) > 1e-4) fx.dir = Math.sign(dp);
    if (dp > 0.02) fx.flash = 0.12;
    // fertig gesägt: zwei Hälften fallen in die Kiste
    if (view.c > pv.c && pv.k >= 0) {
      const log = sched.get(pv.k), half = log.L / 2;
      fx.pieces.push({ x: SAW_X - half / 2, y: BELT_Y, vx: 520, vy: 0, rot: 0, vr: 0, L: half, D: log.D, oak: log.oak, belt: true });
      fx.pieces.push({ x: SAW_X + half / 2 + 4, y: BELT_Y, vx: 600, vy: 0, rot: 0, vr: 0, L: half, D: log.D, oak: log.oak, belt: true });
      fx.logs.delete(pv.k);
      if (snd.events) Sound.cut();
    }
    // Band voll: ein Stamm fällt herunter
    if (view.x > pv.x) {
      const log = sched.get(Math.max(0, sched.spawnedBy(view.t) - 1));
      fx.lost.push({ x: 10, y: BELT_Y, vx: -70, vy: -160, rot: 0, vr: -3, L: log.L, D: log.D, oak: log.oak });
      fx.xflash = 0.9; fx.shake = 0.3;
      const left = CFG.LIVES - view.x;
      banner(fx, view.practice ? 'Stamm verloren!' : left > 0 ? `Stamm verloren! Noch ${left}` : 'Stamm verloren!', 'bad', 1.2);
      if (snd.events) Sound.miss();
    }
    if (view.ph !== pv.ph) {
      if (view.ph === PH.NAIL) { if (snd.events) Sound.alarm(); }
      else if (view.ph === PH.JAM) { fx.shake = 0.2; if (snd.events) Sound.jam(); }
      else if (view.ph === PH.CUT && pv.ph === PH.FEED) { if (snd.events) Sound.clamp(); }
      else if (view.ph === PH.SNAP) { fx.shake = 0.35; if (snd.events) Sound.snap(); }
      else if (view.ph === PH.CUT && pv.ph === PH.NAIL) { banner(fx, 'WEITER!', 'ok', 0.8); if (snd.events) Sound.resume(); }
      else if (view.ph === PH.CUT && pv.ph === PH.SNAP) { banner(fx, 'Geflickt. Weiter!', 'ok', 0.9); if (snd.events) Sound.resume(); }
    }
  }
  // Stämme rollen zu ihrem Platz
  const roll = (L, tx, speed) => { const d = tx - L.x, step = speed * dt; L.x = Math.abs(d) <= step ? tx : L.x + Math.sign(d) * step; };
  const keep = new Set(view.q);
  if (view.k >= 0) keep.add(view.k);
  for (const i of [...fx.logs.keys()]) if (!keep.has(i)) fx.logs.delete(i);
  const get = (i, tx) => { let L = fx.logs.get(i); if (!L) { L = { x: pv ? ENTRY_X : tx }; fx.logs.set(i, L); } return L; };
  let edge = Infinity, ty = YB_UP;
  if (view.k >= 0) {
    const log = sched.get(view.k), L = get(view.k, SAW_X);
    if (view.ph === PH.FEED) {
      // rollt genau so lange, wie das Spiel es vorgibt, und bremst am Schluss
      if (L.from === undefined || L.resume) { L.from = L.x; L.f0 = view.f; L.resume = false; }
      const k = clamp((view.f - L.f0) / Math.max(1e-3, 1 - L.f0), 0, 1);
      L.x = lerp(L.from, SAW_X, 1 - (1 - k) * (1 - k));
    } else if (view.ph === PH.JAM) {
      // zu früh gesägt: Das Seil hängt im Weg, der Stamm prallt dagegen
      L.resume = true;
      roll(L, Math.max(L.x, RX0 - log.L / 2 - 4), 400);
      ty = L.x + log.L / 2 > RX0 + 6 ? BELT_Y - log.D - 2 : BELT_Y - log.D * 0.45;
    } else {
      roll(L, SAW_X, 520);
      if (sawing(view.ph)) ty = BELT_Y - log.D + view.g * log.D;
    }
    edge = L.x - log.L / 2;
  }
  // wartende Stämme bleiben hinter dem Stamm an der Säge
  view.q.forEach((i, j) => {
    const len = sched.get(i).L, tx = Math.min(SLOT_X[Math.min(j, SLOT_X.length - 1)], edge - 8 - len / 2);
    const L = get(i, tx);
    roll(L, tx, 520);
    edge = Math.min(L.x, tx) - len / 2;
  });
  // Seil senkt sich mit dem Schnitt
  fx.yB += (ty - fx.yB) * (1 - Math.exp(-dt / 0.05));
  // Sägemehl fliegt dorthin, wohin das Seil läuft
  if (view.ph === PH.CUT && view.k >= 0 && fx.speed > 0.5 && fx.dust.length < 160) {
    const log = sched.get(view.k);
    let n = fx.speed * dt * 4;
    while (n > 0) {
      if (n >= 1 || Math.random() < n) {
        fx.dust.push({ x: SAW_X + fx.dir * (log.L / 2 + 4), y: fx.yB - 2, vx: fx.dir * (90 + Math.random() * 220), vy: -(30 + Math.random() * 150), life: 0.4 + Math.random() * 0.4, r: 1.5 + Math.random() * 2 });
      }
      n -= 1;
    }
  }
  for (const d of fx.dust) { d.x += d.vx * dt; d.y += d.vy * dt; d.vy += 700 * dt; d.life -= dt; }
  fx.dust = fx.dust.filter(d => d.life > 0);
  for (const pc of fx.pieces) {
    if (pc.belt) { pc.x += pc.vx * dt; if (pc.x - pc.L / 2 > BELT_X1 - 6) { pc.belt = false; pc.vr = 2.5; } }
    else { pc.vy += 1400 * dt; pc.y += pc.vy * dt; pc.x += 60 * dt; pc.rot += pc.vr * dt; }
  }
  fx.pieces = fx.pieces.filter(pc => pc.y - pc.D < STRIP_Y + 10);
  for (const pc of fx.lost) { pc.vy += 1400 * dt; pc.y += pc.vy * dt; pc.x += pc.vx * dt; pc.rot += pc.vr * dt; }
  fx.lost = fx.lost.filter(pc => pc.y - pc.D < STRIP_Y + 10);
  if (fx.banner) fx.banner.age += dt;
  if (fx.win) fx.winT += dt;
  for (const k of fx.confetti) { k.vy = Math.min(k.vy + 220 * dt, 260); k.x += (k.vx + Math.sin(k.y / 30) * 40) * dt; k.y += k.vy * dt; k.rot += k.vr * dt; }
  fx.confetti = fx.confetti.filter(k => k.y < STRIP_Y + 20);
  fx.shake = Math.max(0, fx.shake - dt);
  fx.xflash = Math.max(0, fx.xflash - dt);
  fx.flash = Math.max(0, fx.flash - dt);
  fx.beltOff += 40 * dt;
  if (snd.speed !== undefined) fx.speed = snd.speed;
  const target = view.alive && view.ph !== PH.SNAP ? clamp(fx.speed / 9, 0, 1) : 0;
  fx.lamp += (target - fx.lamp) * (1 - Math.exp(-dt / 0.03));
  fx.prev = { p: view.p, c: view.c, x: view.x, ph: view.ph, k: view.k };
}

/* ---------- Seite ---------- */
const setText = (el, s) => { if (el && el.textContent !== s) el.textContent = s; };
const soundBtn = $('#soundBtn');
function syncSound() { soundBtn.setAttribute('aria-pressed', String(Sound.on)); soundBtn.textContent = Sound.on ? 'Ton an' : 'Ton aus'; }
syncSound();
soundBtn.addEventListener('click', () => {
  Sound.on = !Sound.on;
  try { localStorage.setItem('saegewerk.sound', Sound.on ? '1' : '0'); } catch (_) {}
  if (Sound.on) Sound.ensure(); else Sound.silence();
  syncSound();
});
$('#fullscreen').addEventListener('click', () => {
  if (document.fullscreenElement) document.exitFullscreen().catch(() => {});
  else if (root.requestFullscreen) root.requestFullscreen().catch(() => {});
});
document.addEventListener('pointerdown', () => Sound.ensure(), { once: true });

let current = 'explain';
function showView(v) {
  current = v;
  $('#explain').hidden = v !== 'explain';
  $('#duel').hidden = v !== 'duel';
  $('#tabExplain').setAttribute('aria-current', v === 'explain' ? 'page' : 'false');
  $('#tabDuel').setAttribute('aria-current', v === 'duel' ? 'page' : 'false');
  const want = v === 'explain' ? '#erklaeren' : '';
  if (location.hash !== want) history.replaceState(null, '', location.pathname + location.search + want);
  Sound.silence();
  if (v === 'duel') connect();
}
$('#tabExplain').addEventListener('click', () => showView('explain'));
$('#tabDuel').addEventListener('click', () => showView('duel'));
window.addEventListener('hashchange', () => showView(location.hash === '#erklaeren' ? 'explain' : 'duel'));

/* ---------- Erklärmodus: die Lehrperson steuert die Säge ---------- */
const EX = { role: 'ac', f: 1, plug: false, power: 0.7, phase: 0, base: 0, fx: makeFx() };
EX.sched = new Schedule(5, true, { interval: 4.2, nails: false });
EX.saw = new Sawyer('ac', EX.sched, true, { calm: true, direct: true });
const exCanvas = $('#exCanvas'), exFreq = $('#exFreq'), exPower = $('#exPower');
function exHz() { return EX.role === 'ac' ? (EX.plug ? 50 : EX.f) : 0; }
function exSync() {
  const ac = EX.role === 'ac', f = exHz();
  $('#exPanel').dataset.mode = EX.role;
  $('#exAc').setAttribute('aria-pressed', String(ac));
  $('#exDc').setAttribute('aria-pressed', String(!ac));
  $('#ex50').setAttribute('aria-pressed', String(ac && EX.plug));
  exFreq.disabled = !ac;
  $('#freqBox').classList.toggle('off', !ac);
  setText($('#exFreqOut'), ac ? fmtHz(f) : '–');
  setText($('#exPowerOut'), Math.round(EX.power * 100) + ' %');
  setText($('#exRole'), ROLE_NAME[EX.role]);
  setText($('#exTag'), fmtHz(f));
  setText($('#exName'), ac ? 'Wechselstrom (AC)' : 'Gleichstrom (DC)');
  setText($('#exHz'), fmtHz(f));
  setText($('#exFlips'), ac ? String(r1(f * 2)) : '0');
  setText($('#exExample'), !ac ? 'Batterie, Akku' : EX.plug ? 'Steckdose' : 'Velodynamo');
  let txt;
  if (EX.power === 0) txt = 'Stärke 0: Ohne Antrieb bewegt sich nichts. Kein Strom, kein Licht.';
  else if (!ac) txt = 'Gleichstrom fliesst immer in die gleiche Richtung. Der gelbe Punkt fährt im Kreis herum, die Lampe leuchtet ruhig.';
  else if (EX.plug) txt = '50 Hz: Das Seil wechselt 100-mal pro Sekunde die Richtung. Das sieht kein Auge mehr, die Lampe leuchtet gleichmässig.';
  else if (f <= 2) txt = 'Wechselstrom fährt hin und her. Schaut auf die Lampe: Bei jedem Umkehren steht das Seil kurz still und sie wird dunkler.';
  else txt = 'Je höher die Frequenz, desto öfter wechselt die Richtung. Der gelbe Punkt bleibt am Platz, und trotzdem wird gesägt.';
  setText($('#exText'), txt);
}
function exRole(role) {
  if (role === EX.role) return;
  EX.role = role; EX.saw.role = role;
  EX.base = EX.saw.q; EX.phase = 0;   // kein Sprung beim Umschalten
  exSync();
}
$('#exAc').addEventListener('click', () => exRole('ac'));
$('#exDc').addEventListener('click', () => exRole('dc'));
$('#ex50').addEventListener('click', () => { exRole('ac'); EX.plug = !EX.plug; exSync(); });
exFreq.addEventListener('input', () => { EX.f = Number(exFreq.value); EX.plug = false; exSync(); });
exPower.addEventListener('input', () => { EX.power = Number(exPower.value) / 100; exSync(); });
exSync();

function stepExplain(dt) {
  const s = EX.saw, ac = EX.role === 'ac', A = EX.power, f = exHz(), fast = ac && f > 6;
  let forced;
  if (ac && fast) {
    // zu schnell fürs Auge: Seil verwischt, gesägt wird trotzdem
    s.q = EX.base; s.pulled(4 * A * f * dt); forced = 4 * A * f;
  } else if (ac) {
    EX.phase = (EX.phase + TAU * f * dt) % TAU;
    const q = EX.base + A * Math.sin(EX.phase);
    s.pulled(Math.abs(q - s.q)); s.q = q;
  } else {
    const d = A * 8 * dt;
    s.q += d; s.pulled(d);
  }
  s.step(dt);
  const v = sawView(s); v.x = 0;
  updateFx(EX.fx, v, EX.sched, dt, { events: true, speed: forced });
  Sound.saw('ex', EX.fx.speed);
  const c = fit(exCanvas);
  if (c) drawScene(c, v, EX.sched, EX.fx, { role: EX.role, showHz: true, hz: f, blur: fast ? A : 0, who: ac ? 'AC' : 'DC' });
}

/* ---------- Duell: ein Spiel für alle, zwei sägen, der Rest schaut zu ---------- */
const D = {
  ws: null, open: false, wanted: false, retry: 0,
  you: -1, state: 'lobby', round: 0, dur: 60, players: [null, null], viewers: 0, history: [],
  phase: 'lobby', roles: ['ac', 'dc'], startAt: 0, sched: null, saw: null, practice: null,
  remote: [new Remote(), new Remote()], sendAcc: 0, doneSent: false, result: null, lastCount: 0, overAt: 0,
};
const idleSched = new Schedule(1, true);
const CTL = { ac: 'Maus hin und her bewegen', dc: 'Mausrad drehen' };
const panels = ['#pA', '#pB'].map(sel => {
  const el = $(sel);
  return { el, canvas: $('canvas', el), name: $('[data-name]', el), role: $('[data-role]', el), wait: $('[data-wait]', el), cuts: $('[data-cuts]', el), ctl: $('[data-ctl]', el), fx: makeFx(), key: '' };
});
const nameInput = $('#nameInput'), readyBtn = $('#readyBtn'), watchBtn = $('#watchBtn'), joinMsg = $('#joinMsg');
try { nameInput.value = localStorage.getItem('saegewerk.name') || ''; } catch (_) {}

const slotFor = i => (D.you >= 0 ? (i === 0 ? D.you : 1 - D.you) : i);
const roleOf = slot => (D.phase === 'lobby' ? rolesFor(D.round + 1) : D.roles)[slot];
const nameOf = slot => (D.players[slot] ? D.players[slot].name : 'Platz ' + (slot + 1));
const busy = () => D.phase === 'countdown' || D.phase === 'play';
const clockT = () => clamp((performance.now() - D.startAt) / 1000, 0, D.dur);

function connect() {
  D.wanted = true;
  if (D.ws) return;
  const ws = new WebSocket((location.protocol === 'https:' ? 'wss:' : 'ws:') + '//' + location.host + '/ws');
  D.ws = ws;
  ws.onopen = () => { D.open = true; D.retry = 0; render(); };
  ws.onmessage = e => { let m; try { m = JSON.parse(e.data); } catch (_) { return; } onMessage(m); };
  ws.onclose = () => {
    D.ws = null; D.open = false; D.you = -1;
    if (busy()) toLobby();
    render();
    setTimeout(connect, Math.min(5000, 800 * ++D.retry));
  };
  ws.onerror = () => {};
}
function send(m) { if (D.ws && D.open) D.ws.send(JSON.stringify(m)); }

function toLobby() {
  D.phase = 'lobby'; D.result = null; D.saw = null; D.practice = null;
  $('#countdown').hidden = true; $('#result').hidden = true;
  panels.forEach(p => { resetFx(p.fx); p.key = ''; });
}

function onMessage(m) {
  if (m.t === 'game') {
    const was = D.you;
    Object.assign(D, { you: m.you, state: m.state, round: m.round, dur: m.dur, players: m.players, viewers: m.viewers, history: m.history });
    if (was !== D.you) { D.howSeen = false; panels.forEach(p => { resetFx(p.fx); p.key = ''; }); if (D.you < 0) D.practice = null; }
    if (D.you >= 0) joinMsg.textContent = '';
    renderRounds();
    render();
  } else if (m.t === 'start') {
    toLobby();
    Object.assign(D, { phase: 'countdown', round: m.round, roles: m.roles, dur: m.dur, startAt: performance.now() + m.delay, sendAcc: 0, doneSent: false, lastCount: 0 });
    D.sched = new Schedule(m.seed);
    D.howSeen = false;   // nächste Runde neue Stromart: Anleitung nochmals zeigen
    D.remote.forEach(r => r.reset());
    if (D.you >= 0) D.saw = new Sawyer(D.roles[D.you], D.sched, true, { limit: D.dur });
    render();
  } else if (m.t === 'peer') {
    if (D.phase !== 'lobby') D.remote[m.slot].push(m.s);
  } else if (m.t === 'result') {
    onResult(m);
  } else if (m.t === 'aborted') {
    toLobby();
    joinMsg.textContent = m.msg + ' Die Runde wurde abgebrochen.';
    render();
  } else if (m.t === 'error') {
    joinMsg.textContent = m.msg;
  }
}

// Siegerehrung: Konfetti für den Sieg, danach die Karte
function onResult(m) {
  D.phase = 'over'; D.result = m; D.overAt = performance.now();
  $('#countdown').hidden = true;
  panels.forEach((p, i) => {
    const slot = slotFor(i);
    celebrate(p.fx, m.winner < 0 ? 'tie' : m.winner === slot ? 'win' : 'lose');
  });
  if (D.you >= 0) { if (m.winner === D.you) Sound.win(); else Sound.lose(); }
  else Sound.win();
  setTimeout(() => { if (D.result === m) showResult(m); }, 1600);
  render();
}
function showResult(m) {
  const card = $('#resultCard');
  card.dataset.mode = m.winner >= 0 ? m.roles[m.winner] : '';
  setText($('#resultRound'), 'Runde ' + m.n);
  setText($('#resultTitle'), m.winner < 0 ? 'Unentschieden!' : m.winner === D.you ? 'Du gewinnst!' : m.names[m.winner] + ' gewinnt!');
  const line = i => `${m.names[i]} (${ROLE_NAME[m.roles[i]]}): ${m.cuts[i]} ${m.cuts[i] === 1 ? 'Stamm' : 'Stämme'}`;
  setText($('#resultText'), line(0) + ' · ' + line(1) + '. Nächste Runde wird die Stromart getauscht.');
  $('#againBtn').hidden = D.you < 0;
  $('#result').hidden = false;
}
$('#againBtn').addEventListener('click', () => { toLobby(); send({ t: 'ready' }); render(); });
// Gegner nur als kleiner Zähler, damit man sich auf die eigene Säge konzentriert
function oppText() {
  if (D.you < 0) return '';
  const o = D.players[1 - D.you];
  if (!o) return 'Gegner: noch niemand';
  if (D.phase === 'lobby') return `Gegner: ${o.name}${o.ready ? ' ✓ bereit' : ' liest noch'}`;
  const last = D.remote[1 - D.you].latest, c = D.result ? D.result.cuts[1 - D.you] : last ? last.c : 0;
  return `${o.name}: ${c} ${c === 1 ? 'Stamm' : 'Stämme'}`;
}
$('#closeResult').addEventListener('click', () => { toLobby(); render(); });

readyBtn.addEventListener('click', () => {
  Sound.ensure();
  if (D.you < 0) {
    const name = nameInput.value.trim();
    if (!name) { joinMsg.textContent = 'Gib zuerst deinen Namen ein.'; nameInput.focus(); return; }
    try { localStorage.setItem('saegewerk.name', name); } catch (_) {}
    send({ t: 'join', name });
  } else {
    if (D.phase === 'over') toLobby();
    send({ t: 'ready' });
  }
});
nameInput.addEventListener('keydown', e => { if (e.key === 'Enter') readyBtn.click(); });
watchBtn.addEventListener('click', () => { send({ t: 'watch' }); toLobby(); });
$('#howReady').addEventListener('click', () => { Sound.ensure(); D.howSeen = true; send({ t: 'ready' }); });
$('#howPractice').addEventListener('click', () => { Sound.ensure(); D.howSeen = true; render(); });
$('#howWatch').addEventListener('click', () => watchBtn.click());

// Knöpfe, Namen und Texte, wenn sich am Spiel etwas ändert
function render() {
  const me = D.you >= 0 ? D.players[D.you] : null, other = D.you >= 0 ? D.players[1 - D.you] : null;
  const free = D.players.filter(p => !p).length;
  $('#nameField').hidden = !!me;
  nameInput.disabled = !D.open || (!me && free === 0);
  watchBtn.hidden = !me;
  // Spieler üben, bis sie selbst auf Bereit klicken. Erst wenn beide bereit sind, startet die Runde.
  readyBtn.hidden = !!me && (me.ready || D.phase !== 'lobby' || !D.howSeen);
  readyBtn.textContent = me ? 'Bereit' : 'Mitspielen';
  readyBtn.disabled = !D.open || (!me && free === 0);
  // Anleitung vor dem Bereit: nur die eigene Säge, Stromart, Steuerung und Ziel
  const how = !!me && !me.ready && D.phase === 'lobby' && !D.howSeen;
  $('#howTo').hidden = !how;
  if (how) {
    const role = roleOf(D.you);
    $('#howCard').dataset.mode = role;
    setText($('#howRole'), ROLE_NAME[role]);
    setText($('#howCtl'), role === 'ac' ? 'Maus hin und her bewegen: Das Seil fährt hin und her.' : 'Mausrad drehen, immer weiter: Das Seil läuft im Kreis.');
    setText($('#howGoal'), `Ziel: In einer Minute mehr Stämme durchsägen als ${other ? other.name : 'die andere Person'}.`);
    setText($('#howWhy'), role === 'ac' ? 'Wechselstrom wechselt dauernd die Richtung, sägt aber trotzdem.' : 'Gleichstrom fliesst immer in die gleiche Richtung.');
  }
  $('#arena').classList.toggle('solo', !!me);
  let st;
  if (!D.open) st = D.retry ? 'Keine Verbindung. Neuer Versuch …' : 'Verbinde mit dem Server …';
  else if (D.phase === 'countdown') st = 'Achtung, gleich geht es los!';
  else if (D.phase === 'play') st = `${nameOf(0)} gegen ${nameOf(1)}: Wer sägt mehr Stämme?`;
  else if (D.phase === 'over' && D.result) st = D.result.winner < 0 ? 'Unentschieden!' : D.result.names[D.result.winner] + ' gewinnt!';
  else if (me) st = me.ready ? (other ? `Du bist bereit. Warte auf ${other.name} … Bis dahin kannst du üben.` : 'Du bist bereit. Warte auf eine zweite Person … Bis dahin kannst du üben.') : (D.howSeen ? 'Übe, so lange du willst, und klicke dann auf Bereit.' : 'Lies die Anleitung.');
  else if (free === 2) st = 'Zwei Plätze frei: Name eingeben und Mitspielen klicken.';
  else if (free === 1) st = 'Ein Platz ist frei: Name eingeben und Mitspielen klicken.';
  else st = `Du schaust zu: ${nameOf(0)} gegen ${nameOf(1)}.`;
  setText($('#status'), st);
  const chip = $('#viewerChip');
  chip.hidden = !D.viewers;
  setText(chip, D.viewers === 1 ? '1 Person schaut zu' : D.viewers + ' Personen schauen zu');
  if (!me && free === 0 && D.open && !joinMsg.textContent) joinMsg.textContent = 'Beide Plätze sind besetzt. Du schaust zu, bis einer frei wird.';
  if (!me && free > 0 && joinMsg.textContent.startsWith('Beide Plätze')) joinMsg.textContent = '';
}
function renderRounds() {
  const body = $('#roundsBody');
  body.textContent = '';
  if (!D.history.length) { body.innerHTML = '<tr><td class="empty" colspan="4">Noch keine Runde gespielt.</td></tr>'; return; }
  for (const h of D.history.slice().reverse()) {
    const tr = document.createElement('tr');
    const cell = (txt, cls) => { const td = document.createElement('td'); td.textContent = txt; if (cls) td.className = cls; tr.appendChild(td); };
    const ai = h.roles.indexOf('ac'), di = 1 - ai;
    cell(String(h.n));
    cell(`${h.names[ai]} · ${h.cuts[ai]}`, h.winner === ai ? 'win' : '');
    cell(`${h.names[di]} · ${h.cuts[di]}`, h.winner === di ? 'win' : '');
    cell(h.winner < 0 ? 'Unentschieden' : h.names[h.winner]);
    body.appendChild(tr);
  }
}

const fmtTime = s => { const n = Math.max(0, Math.ceil(s)); return Math.floor(n / 60) + ':' + String(n % 60).padStart(2, '0'); };
function stepDuel(now, dt) {
  const T = clockT();
  // Countdown
  if (D.phase === 'countdown') {
    const left = (D.startAt - now) / 1000, n = Math.ceil(left);
    if (n !== D.lastCount) { D.lastCount = n; if (n > 0) Sound.beep(false); }
    if (left <= 0) { D.phase = 'play'; D.lastCount = 0; Sound.beep(true); D.losAt = now; render(); }
    $('#countdown').hidden = false; setText($('#countText'), String(Math.max(1, n)));
  } else if (D.phase === 'play' && now - (D.losAt || 0) < 700) {
    $('#countdown').hidden = false; setText($('#countText'), 'Los!');
  } else $('#countdown').hidden = true;
  // eigene Säge
  if (D.phase === 'play' && D.saw) {
    const run = Math.min(D.dur + 0.1, (now - D.startAt) / 1000);
    D.saw.step(clamp(run - D.saw.t - D.saw.acc, 0, 1.5));
    D.sendAcc += dt;
    const s = D.saw;
    if (D.sendAcc >= 1 / CFG.SEND_HZ || s.over) {
      D.sendAcc = 0;
      send({ t: 'state', s: { t: r3(s.t), p: r3(s.p), g: r3(s.g), f: r3(s.f), ph: s.ph, pt: r3(s.pt), k: s.k, q: s.queue, c: s.c, x: s.x, a: s.alive ? 1 : 0 } });
    }
    if (s.over && !D.doneSent) { D.doneSent = true; send({ t: 'done', c: s.c }); }
  }
  // Uhr
  const remain = D.phase === 'play' ? D.dur - T : D.phase === 'over' ? 0 : D.dur;
  const timer = $('#timer');
  setText(timer, fmtTime(remain));
  timer.classList.toggle('hot', D.phase === 'play' && remain <= 10);
  if (D.phase === 'play') {
    const sec = Math.ceil(remain);
    if (sec !== D.lastSec) { D.lastSec = sec; if (sec <= 5 && sec > 0) Sound.beep(false); }
  }
  // Zuschauer: nach dem Ergebnis irgendwann zurück zur Wartebühne
  if (D.phase === 'over' && D.you < 0 && now - D.overAt > 12000) toLobby();
  // Übungssäge in der Wartezeit
  if (D.phase === 'lobby' && D.you >= 0) {
    const role = roleOf(D.you);
    if (!D.practice || D.practice.role !== role) D.practice = new Sawyer(role, new Schedule(newSeed(), true), true);
    D.practice.step(dt);
  }
  const oc = $('#oppChip'), ot = oppText();
  oc.hidden = !ot; setText(oc, ot);
  panels.forEach((p, i) => { if (i === 0 || D.you < 0) drawPanel(p, slotFor(i), T, dt); });
}

function drawPanel(p, slot, T, dt) {
  const pl = D.players[slot], role = roleOf(slot), mine = slot === D.you;
  p.el.dataset.mode = role;
  p.el.classList.toggle('me', mine);
  setText(p.name, pl ? pl.name + (D.phase === 'lobby' && pl.ready ? ' ✓' : '') : 'Platz frei');
  setText(p.role, ROLE_NAME[role]);
  setText(p.ctl, CTL[role]);
  const empty = !pl && D.phase === 'lobby';
  p.wait.hidden = !empty;
  // eigene Säge, Übungssäge, Säge aus dem Netz oder leere Halle
  let view, sched = idleSched, hint = null, tag = '';
  if (D.phase === 'lobby') {
    if (mine && D.practice) { view = sawView(D.practice); sched = D.practice.sched; tag = pl && pl.ready ? 'ÜBEN · WARTE AUF DIE ANDERE PERSON' : 'ÜBEN, BIS DU BEREIT BIST'; }
    else { view = idleView(); if (pl) hint = { big: pl.ready ? 'BEREIT!' : 'NOCH NICHT BEREIT', small: pl.name }; }
  } else {
    sched = D.sched;
    if (mine && D.saw) view = sawView(D.saw);
    else view = D.remote[slot].sample(D.phase === 'over' ? D.dur : T - CFG.DELAY) || idleView();
    if (D.phase === 'countdown') hint = { big: ROLE_NAME[role].toUpperCase(), small: CTL[role] };
    if (D.result) view = Object.assign({}, view, { c: D.result.cuts[slot] });
  }
  const key = D.phase + '|' + slot + '|' + D.round + '|' + (mine && D.practice ? 'p' : '');
  if (key !== p.key && !(p.key.startsWith('play|') && D.phase === 'over')) { if (!p.fx.win) resetFx(p.fx); }
  p.key = key;
  setText(p.cuts, String(view.c));
  updateFx(p.fx, view, sched, dt, { events: mine || D.you < 0 });
  if (mine) Sound.saw('me', current === 'duel' ? p.fx.speed : 0);
  if (empty) return;
  const c = fit(p.canvas);
  if (c) drawScene(c, view, sched, p.fx, { role, mouse: true, who: role === 'ac' ? 'AC' : 'DC', hint, tag });
}

// Maus: Wechselstrom mit der Bewegung, Gleichstrom mit dem Rad
const mySaw = () => (current !== 'duel' || D.you < 0 ? null : D.phase === 'play' ? D.saw : D.phase === 'lobby' ? D.practice : null);
window.addEventListener('mousemove', e => {
  const s = mySaw();
  if (s && s.role === 'ac' && e.movementX) s.move(clamp(e.movementX * CFG.MOUSE, -1, 1));
});
window.addEventListener('wheel', e => {
  if (current !== 'duel' || D.you < 0) return;
  const own = e.target instanceof Node && panels[0].el.contains(e.target);
  if (busy() || own) e.preventDefault();
  const s = mySaw();
  if (!s || s.role !== 'dc') return;
  const px = e.deltaMode === 1 ? e.deltaY * 33 : e.deltaMode === 2 ? e.deltaY * 400 : e.deltaY;
  if (px) s.move(Math.abs(px) / 100 * CFG.WHEEL);
}, { passive: false });
window.addEventListener('keydown', e => {
  if (e.target === nameInput || !mySaw()) return;
  if (['ArrowLeft', 'ArrowRight', 'ArrowUp', 'ArrowDown', 'a', 'd', ' '].includes(e.key)) {
    banner(panels[0].fx, mySaw().role === 'ac' ? 'Maus hin und her!' : 'Mausrad drehen!', 'warn', 1, true);
    if (e.key.startsWith('Arrow') || e.key === ' ') e.preventDefault();
  }
});

/* ---------- Hauptschleife ---------- */
let lastNow = performance.now();
function tick(now) {
  const dt = clamp((now - lastNow) / 1000, 0, 0.05);
  lastNow = now;
  if (current === 'explain') stepExplain(dt); else stepDuel(now, dt);
}
function frame(now) { tick(now); requestAnimationFrame(frame); }
// Im Hintergrund läuft kein requestAnimationFrame: die Runde muss trotzdem zu Ende gehen
setInterval(() => { const now = performance.now(); if (now - lastNow > 300) tick(now); }, 250);
showView(location.hash === '#erklaeren' ? 'explain' : 'duel');
requestAnimationFrame(frame);
})();
