'use strict';
/* --- 00_util.js --- */
/* ===== Общие утилиты ===== */
const G = 9.81, SOUND = 343;
const clamp = (v, a, b) => v < a ? a : v > b ? b : v;
const lerp = (a, b, t) => a + (b - a) * t;
const rnd = (a = 0, b = 1) => a + Math.random() * (b - a);
const rndi = (a, b) => Math.floor(a + Math.random() * (b - a + 1));
const pick = a => a[Math.floor(Math.random() * a.length)];
const sm01 = t => { t = clamp(t, 0, 1); return t * t * (3 - 2 * t); };
const damp = (cur, target, rate, dt) => cur + (target - cur) * (1 - Math.exp(-rate * dt));
const wrapAngle = a => { while (a > Math.PI) a -= Math.PI * 2; while (a < -Math.PI) a += Math.PI * 2; return a; };

const V = {
  add: (a, b) => [a[0] + b[0], a[1] + b[1], a[2] + b[2]],
  sub: (a, b) => [a[0] - b[0], a[1] - b[1], a[2] - b[2]],
  mul: (a, s) => [a[0] * s, a[1] * s, a[2] * s],
  mad: (a, b, s) => [a[0] + b[0] * s, a[1] + b[1] * s, a[2] + b[2] * s],
  dot: (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2],
  cross: (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]],
  len: a => Math.hypot(a[0], a[1], a[2]),
  dist: (a, b) => Math.hypot(a[0] - b[0], a[1] - b[1], a[2] - b[2]),
  norm: a => { const l = Math.hypot(a[0], a[1], a[2]) || 1; return [a[0] / l, a[1] / l, a[2] / l]; },
  lerp: (a, b, t) => [a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t, a[2] + (b[2] - a[2]) * t],
};

// yaw=0 смотрит в -Z, положительный yaw — поворот влево
function fwdVec(yaw, pitch) {
  const cp = Math.cos(pitch);
  return [-Math.sin(yaw) * cp, Math.sin(pitch), -Math.cos(yaw) * cp];
}

// детерминированный ГПСЧ для генерации карты
let _seed = 1337;
function srand(s) { _seed = s >>> 0; }
function srnd() {
  _seed = (_seed + 0x6D2B79F5) | 0;
  let t = Math.imul(_seed ^ (_seed >>> 15), 1 | _seed);
  t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
  return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
}
const srr = (a, b) => a + srnd() * (b - a);

const Bus = {
  h: {},
  on(t, f) { (this.h[t] || (this.h[t] = [])).push(f); },
  emit(t, a) { const l = this.h[t]; if (l) for (let i = 0; i < l.length; i++) l[i](a); },
};

const Game = {
  combatants: [], player: null, time: 0, running: false, paused: false,
  mode: 'team', difficulty: 1, botCount: 8, over: false,
};

if (typeof module !== 'undefined') { /* для тестов в Node */ }

/* --- 10_world.js --- */
/* ===== Мир: коллайдеры, трассировка, навигация, генерация карты ===== */
const MATS = {
  // cost — «стоимость» одного метра материала в единицах пробития (pen)
  concrete: { cost: 1500, fx: 'dust', snd: 'stone', hard: true },
  brick:    { cost: 1000, fx: 'dust', snd: 'stone', hard: true },
  plaster:  { cost: 450,  fx: 'dust', snd: 'stone', hard: false },
  drywall:  { cost: 130,  fx: 'dust', snd: 'stone', hard: false },
  wood:     { cost: 330,  fx: 'wood', snd: 'wood',  hard: false },
  metal:    { cost: 3000, fx: 'spark', snd: 'metal', hard: true },
  sand:     { cost: 520,  fx: 'dust', snd: 'dirt',  hard: false },
  dirt:     { cost: 800,  fx: 'dirt', snd: 'dirt',  hard: false },
  roof:     { cost: 1500, fx: 'dust', snd: 'stone', hard: true },
};

const MAPS = {};
const World = {
  boxes: [], deco: [], rooms: [], pickups: [], roads: [], lights: [], trees: [], buildings: [], signs: [], flat: [], hintWP: [], koth: [],
  bound: 118, cs: 0.6, stamp: 0, spawnPlayer: [0, 106], LH: 3.2, T: 120,
  waypoints: [], botSpawns: [],
};
World.reset = function (id) {
  const cfg = MAPS[id] || MAPS.poly;
  Object.assign(this, {
    boxes: [], deco: [], rooms: [], pickups: [], roads: [], lights: [], trees: [], buildings: [], signs: [], flat: [], hintWP: [], waypoints: [], botSpawns: [],
    mapId: MAPS[id] ? id : 'poly', mapName: cfg.name, bound: cfg.bound, spawnPlayer: cfg.spawn.slice(), T: cfg.T, pickN: cfg.pick, maxWP: cfg.maxWP,
    spawnMin: cfg.spawnMin || 55, env: cfg.env, koth: cfg.koth.map(k => k.slice()), hg: null,
  });
};
World.pathSpent = 0;
World.clock = () => (typeof performance !== 'undefined' ? performance.now() : Date.now());
World.generate = function (id) {
  this.reset(id);
  MAPS[this.mapId].gen.call(this);
  this.buildTerrain();
  this.buildGrid();
  this.buildNav();
  this.flood();
  this.placePickups();
};
const CELL = 6, OFF = 130, NC = 44;
const STEP = 0.5;
const ci = v => clamp(Math.floor((v + OFF) / CELL), 0, NC - 1);

function B(x, y, z, w, h, d, mat, col, opt) {
  const b = { x0: x - w / 2, x1: x + w / 2, y0: y, y1: y + h, z0: z - d / 2, z1: z + d / 2, mat, col: col === undefined ? 0xffffff : col, stamp: 0 };
  if (opt) Object.assign(b, opt);
  World.boxes.push(b);
  return b;
}

// декор только для отрисовки: плинтусы, наличники, рамы, лампы — без столкновений и без влияния на пули и навигацию
function D(x, y, z, w, h, d, mat, col, opt) {
  const b = { x0: x - w / 2, x1: x + w / 2, y0: y, y1: y + h, z0: z - d / 2, z1: z + d / 2, mat, col: col === undefined ? 0xffffff : col, deco: true };
  if (opt) Object.assign(b, opt);
  World.deco.push(b);
  return b;
}

/* ---------- сетка и трассировка ---------- */
World.buildGrid = function () {
  this.grid = Array.from({ length: NC * NC }, () => []);
  this.boxes.forEach((b, i) => {
    b.id = i;
    const a = ci(b.x0), c = ci(b.x1), d = ci(b.z0), e = ci(b.z1);
    for (let z = d; z <= e; z++) for (let x = a; x <= c; x++) this.grid[z * NC + x].push(b);
  });
};

function rayBox(b, ox, oy, oz, dx, dy, dz, len) {
  let tmin = -Infinity, tmax = Infinity, nx = 0, ny = 0, nz = 0;
  if (Math.abs(dx) < 1e-9) { if (ox < b.x0 || ox > b.x1) return null; }
  else {
    let t1 = (b.x0 - ox) / dx, t2 = (b.x1 - ox) / dx, n = -1;
    if (t1 > t2) { const q = t1; t1 = t2; t2 = q; n = 1; }
    if (t1 > tmin) { tmin = t1; nx = n; ny = 0; nz = 0; }
    if (t2 < tmax) tmax = t2;
    if (tmin > tmax) return null;
  }
  if (Math.abs(dy) < 1e-9) { if (oy < b.y0 || oy > b.y1) return null; }
  else {
    let t1 = (b.y0 - oy) / dy, t2 = (b.y1 - oy) / dy, n = -1;
    if (t1 > t2) { const q = t1; t1 = t2; t2 = q; n = 1; }
    if (t1 > tmin) { tmin = t1; nx = 0; ny = n; nz = 0; }
    if (t2 < tmax) tmax = t2;
    if (tmin > tmax) return null;
  }
  if (Math.abs(dz) < 1e-9) { if (oz < b.z0 || oz > b.z1) return null; }
  else {
    let t1 = (b.z0 - oz) / dz, t2 = (b.z1 - oz) / dz, n = -1;
    if (t1 > t2) { const q = t1; t1 = t2; t2 = q; n = 1; }
    if (t1 > tmin) { tmin = t1; nx = 0; ny = 0; nz = n; }
    if (t2 < tmax) tmax = t2;
    if (tmin > tmax) return null;
  }
  if (tmax < 0 || tmin > len || tmin < 0) return null;
  return { t: tmin, tExit: tmax, nx, ny, nz, box: b };
}

// ближайшее пересечение отрезка (d — единичный вектор) с коробками
World.rayBoxes = function (ox, oy, oz, dx, dy, dz, len) {
  const st = ++this.stamp;
  let best = null, bt = len;
  let cx = ci(ox), cz = ci(oz);
  const sx = dx > 0 ? 1 : -1, sz = dz > 0 ? 1 : -1;
  const tdx = dx !== 0 ? CELL / Math.abs(dx) : Infinity, tdz = dz !== 0 ? CELL / Math.abs(dz) : Infinity;
  let nx = dx > 0 ? ((cx + 1) * CELL - OFF - ox) / dx : dx < 0 ? (cx * CELL - OFF - ox) / dx : Infinity;
  let nz = dz > 0 ? ((cz + 1) * CELL - OFF - oz) / dz : dz < 0 ? (cz * CELL - OFF - oz) / dz : Infinity;
  for (let guard = 0; guard < 200; guard++) {
    const cell = this.grid[cz * NC + cx];
    for (let i = 0; i < cell.length; i++) {
      const b = cell[i];
      if (b.stamp === st) continue;
      b.stamp = st;
      const h = rayBox(b, ox, oy, oz, dx, dy, dz, bt);
      if (h && h.t < bt) { bt = h.t; best = h; }
    }
    const tn = Math.min(nx, nz);
    if (tn >= bt || tn >= len) break;
    if (nx < nz) { cx += sx; nx += tdx; } else { cz += sz; nz += tdz; }
    if (cx < 0 || cz < 0 || cx >= NC || cz >= NC) break;
  }
  return best;
};

World.ray = function (ox, oy, oz, dx, dy, dz, len) {
  const h = this.rayBoxes(ox, oy, oz, dx, dy, dz, len);
  const th = this.rayTerrain(ox, oy, oz, dx, dy, dz, h ? h.t : len);
  if (th && (!h || th.t < h.t)) return { t: th.t, tExit: th.t + 1, nx: th.nx, ny: th.ny, nz: th.nz, box: TERRAIN_BOX };
  return h;
};

// есть ли прямая видимость между точками
World.los = function (a, b) {
  const dx = b[0] - a[0], dy = b[1] - a[1], dz = b[2] - a[2];
  const l = Math.hypot(dx, dy, dz);
  if (l < 0.01) return true;
  return !this.ray(a[0], a[1], a[2], dx / l, dy / l, dz / l, l - 0.02);
};

/* ---------- движение тел ---------- */
function circleAABB(x, z, r, b) {
  const cx = x < b.x0 ? b.x0 : x > b.x1 ? b.x1 : x;
  const cz = z < b.z0 ? b.z0 : z > b.z1 ? b.z1 : z;
  const dx = x - cx, dz = z - cz;
  return dx * dx + dz * dz < r * r;
}
World.blockedAt = function (x, y, z, r, h) {
  if (this.H(x, z) > y + STEP + 0.1) return TERRAIN_BOX;
  const a = ci(x - r), c = ci(x + r), d = ci(z - r), e = ci(z + r);
  for (let j = d; j <= e; j++) for (let i = a; i <= c; i++) {
    const cell = this.grid[j * NC + i];
    for (let k = 0; k < cell.length; k++) {
      const b = cell[k];
      if (b.y1 <= y + STEP || b.y0 >= y + h) continue;
      if (circleAABB(x, z, r, b)) return b;
    }
  }
  return null;
};
World.groundH = function (x, z, r, maxTop) {
  let g = this.H(x, z);
  if (g > maxTop) g = -1e9;
  const a = ci(x - r), c = ci(x + r), d = ci(z - r), e = ci(z + r);
  for (let j = d; j <= e; j++) for (let i = a; i <= c; i++) {
    const cell = this.grid[j * NC + i];
    for (let k = 0; k < cell.length; k++) {
      const b = cell[k];
      if (b.y1 > g && b.y1 <= maxTop && circleAABB(x, z, r * 0.85, b)) g = b.y1;
    }
  }
  return g < -1e8 ? this.H(x, z) : g;
};
World.ceilingAt = function (x, z, r, yTop, vy) {
  const a = ci(x - r), c = ci(x + r), d = ci(z - r), e = ci(z + r);
  for (let j = d; j <= e; j++) for (let i = a; i <= c; i++) {
    const cell = this.grid[j * NC + i];
    for (let k = 0; k < cell.length; k++) {
      const b = cell[k];
      if (b.y0 >= yTop - 0.25 && b.y0 <= yTop + vy + 0.05 && circleAABB(x, z, r * 0.9, b)) return true;
    }
  }
  return false;
};

/* ---------- навигация по поверхностям (несколько этажей) ---------- */
const NAV_R = 0.42, NAV_STEP = 0.52, NAV_HEAD = 1.65;
World.buildNav = function () {
  const cs = this.cs, B_ = this.bound, n = Math.ceil(2 * B_ / cs) + 1, R = NAV_R;
  this.nn = n;
  const start = new Int32Array(n * n + 1), ys = [], cells = [];
  const m = Math.ceil(2 / cs);
  const cand = [];
  for (let j = 0; j < n; j++) for (let i = 0; i < n; i++) {
    const cid = j * n + i;
    start[cid] = ys.length;
    if (i < m || j < m || i >= n - m || j >= n - m) continue;
    const x = -B_ + (i + 0.5) * cs, z = -B_ + (j + 0.5) * cs;
    const a = ci(x - R), c = ci(x + R), d = ci(z - R), e = ci(z + R);
    cand.length = 0;
    if (this.hg) { const nn = this.Hn(x, z); if (nn[1] >= 0.88) cand.push(this.H(x, z)); } else cand.push(0);
    const cz0 = ci(z), cx0 = ci(x), own = this.grid[cz0 * NC + cx0];
    for (let k = 0; k < own.length; k++) {
      const b = own[k];
      if (b.vis === false || b.nonav) continue;
      if (x >= b.x0 && x <= b.x1 && z >= b.z0 && z <= b.z1) cand.push(b.y1);
    }
    if (!cand.length) continue;
    cand.sort((p, q) => p - q);
    let last = -1e9;
    for (let q = 0; q < cand.length; q++) {
      const y = cand[q];
      if (y - last < 0.12) continue;
      let blocked = false;
      for (let k = 0; k < own.length; k++) {
        const b = own[k];
        if (x >= b.x0 && x <= b.x1 && z >= b.z0 && z <= b.z1 && b.y0 < y - 0.02 && b.y1 > y + 0.02) { blocked = true; break; }
      }
      if (blocked) continue;
      for (let jj = d; jj <= e && !blocked; jj++) for (let ii = a; ii <= c && !blocked; ii++) {
        const cell = this.grid[jj * NC + ii];
        for (let k = 0; k < cell.length; k++) {
          const b = cell[k];
          if (b.y1 > y + 0.45 && b.y0 < y + NAV_HEAD && x > b.x0 - R && x < b.x1 + R && z > b.z0 - R && z < b.z1 + R) { blocked = true; break; }
        }
      }
      if (blocked) continue;
      last = y; ys.push(y); cells.push(cid);
    }
  }
  start[n * n] = ys.length;
  this.sStart = start; this.sY = Float32Array.from(ys); this.sCell = Int32Array.from(cells);
  const N = ys.length;
  this.g = new Float32Array(N); this.par = new Int32Array(N);
  this.seen = new Int32Array(N); this.closed = new Int32Array(N); this.pst = 0;
  // соседи узлов считаем один раз: поиск пути потом работает по готовым связям
  const adj = this.adj = new Int32Array(N * 8).fill(-1);
  const DI = [1, -1, 0, 0, 1, 1, -1, -1], DJ = [0, 0, 1, -1, 1, -1, 1, -1];
  for (let k = 0; k < N; k++) {
    const cc = cells[k], i = cc % n, j = (cc / n) | 0, y = this.sY[k];
    for (let d = 0; d < 8; d++) {
      const a = i + DI[d], b = j + DJ[d];
      if (a < 0 || b < 0 || a >= n || b >= n) continue;
      const nn = this.nodeNear(b * n + a, y, NAV_STEP);
      if (nn < 0) continue;
      if (d >= 4 && (this.nodeNear(j * n + a, y, NAV_STEP) < 0 || this.nodeNear(b * n + i, y, NAV_STEP) < 0)) continue;
      adj[k * 8 + d] = nn;
    }
  }
};
World.cellOf = function (x) { return clamp(Math.floor((x + this.bound) / this.cs), 0, this.nn - 1); };
World.cellPos = function (i) { return -this.bound + (i + 0.5) * this.cs; };
World.nodeNear = function (c, y, tol) {
  let best = -1, bd = tol + 1e-6;
  for (let k = this.sStart[c], e = this.sStart[c + 1]; k < e; k++) { const d = Math.abs(this.sY[k] - y); if (d < bd) { bd = d; best = k; } }
  return best;
};
World.surfAt = function (x, z, y, tol) { return this.nodeNear(this.cellOf(z) * this.nn + this.cellOf(x), y, tol === undefined ? NAV_STEP : tol); };
World.isFree = function (x, z, y) { if (y === undefined) y = this.H(x, z); return this.surfAt(x, z, y, 0.7) >= 0; };
World.nodeX = function (k) { return this.cellPos(this.sCell[k] % this.nn); };
World.nodeZ = function (k) { return this.cellPos((this.sCell[k] / this.nn) | 0); };
World.nearestNode = function (x, z, y, needReach) {
  const n = this.nn, i0 = this.cellOf(x), j0 = this.cellOf(z), rc = needReach && this.reach;
  for (let r = 0; r < 16; r++) {
    let best = -1, bd = 1e9;
    for (let dj = -r; dj <= r; dj++) for (let di = -r; di <= r; di++) {
      if (Math.max(Math.abs(di), Math.abs(dj)) !== r) continue;
      const a = i0 + di, b = j0 + dj;
      if (a < 0 || b < 0 || a >= n || b >= n) continue;
      let k = this.nodeNear(b * n + a, y, 1.3);
      if (k >= 0 && rc && !rc[k]) { k = -1; for (let q = this.sStart[b * n + a], e = this.sStart[b * n + a + 1], bd2 = 1.3; q < e; q++) { const dd = Math.abs(this.sY[q] - y); if (rc[q] && dd < bd2) { bd2 = dd; k = q; } } }
      if (k >= 0) { const d = Math.abs(this.sY[k] - y) + Math.hypot(di, dj) * 0.01; if (d < bd) { bd = d; best = k; } }
    }
    if (best >= 0) return best;
  }
  return -1;
};
World.nodeLOS = function (a, b) {
  const n = this.nn, ca = this.sCell[a], cb = this.sCell[b];
  const i0 = ca % n, j0 = (ca / n) | 0, i1 = cb % n, j1 = (cb / n) | 0;
  const steps = Math.max(Math.abs(i1 - i0), Math.abs(j1 - j0), 1);
  let y = this.sY[a];
  for (let k = 1; k <= steps; k++) {
    const i = Math.round(i0 + (i1 - i0) * k / steps), j = Math.round(j0 + (j1 - j0) * k / steps);
    const q = this.nodeNear(j * n + i, y, NAV_STEP);
    if (q < 0) return false;
    y = this.sY[q];
  }
  return Math.abs(y - this.sY[b]) < 0.3;
};
World.findPath = function (sx, sz, tx, tz, maxN, sy, ty) {
  maxN = maxN || 16000;
  if (sy === undefined) sy = this.H(sx, sz);
  if (ty === undefined) ty = sy;
  const n = this.nn, g = this.g, par = this.par, seen = this.seen, closed = this.closed, sY = this.sY, sCell = this.sCell, adj = this.adj;
  const start = this.nearestNode(sx, sz, sy, false), goal = this.nearestNode(tx, tz, ty, true);
  if (start < 0 || goal < 0) return null;
  if (start === goal) return [[this.nodeX(goal), this.nodeZ(goal), sY[goal]]];
  const st = ++this.pst;
  const HI = this._hi || (this._hi = new Int32Array(300000)), HF = this._hf || (this._hf = new Float32Array(300000)), CAP = HI.length;
  let hn = 0;
  const push = (idx, f) => {
    if (hn >= CAP - 1) return;
    let k = hn++;
    while (k > 0) { const p = (k - 1) >> 1; if (HF[p] <= f) break; HI[k] = HI[p]; HF[k] = HF[p]; k = p; }
    HI[k] = idx; HF[k] = f;
  };
  const gc = sCell[goal], gi = gc % n, gj = (gc / n) | 0, gY = sY[goal];
  const s0 = sCell[start];
  g[start] = 0; par[start] = -1; seen[start] = st;
  push(start, 0);
  let found = false, cnt = 0;
  const W_ = this.hW || 1.6;
  let best = start, bestH = 1e9;
  while (hn > 0 && cnt++ < maxN) {
    const cur = HI[0];
    hn--;
    if (hn > 0) {
      const li = HI[hn], lf = HF[hn];
      let k = 0;
      for (;;) {
        let c = 2 * k + 1; if (c >= hn) break;
        if (c + 1 < hn && HF[c + 1] < HF[c]) c++;
        if (HF[c] >= lf) break;
        HI[k] = HI[c]; HF[k] = HF[c]; k = c;
      }
      HI[k] = li; HF[k] = lf;
    }
    if (closed[cur] === st) continue;
    closed[cur] = st;
    if (cur === goal) { found = true; break; }
    { const cc0 = sCell[cur], hx = Math.abs((cc0 % n) - gi), hz = Math.abs(((cc0 / n) | 0) - gj), hv = (hx + hz) - 0.586 * Math.min(hx, hz) + 1.5 * Math.abs(gY - sY[cur]); if (hv < bestH) { bestH = hv; best = cur; } }
    const cy = sY[cur], gcur = g[cur], base = cur * 8;
    for (let k = 0; k < 8; k++) {
      const ni = adj[base + k];
      if (ni < 0 || closed[ni] === st) continue;
      const dy = sY[ni] - cy;
      const ng = gcur + (k < 4 ? 1 : 1.414) + (dy < 0 ? -dy : dy) * 1.5;
      if (seen[ni] !== st || ng < g[ni]) {
        seen[ni] = st; g[ni] = ng; par[ni] = cur;
        const cc = sCell[ni], ddx = Math.abs((cc % n) - gi), ddz = Math.abs(((cc / n) | 0) - gj);
        push(ni, ng + W_ * ((ddx + ddz) - 0.586 * Math.min(ddx, ddz)) + 1.5 * Math.abs(gY - sY[ni]));
      }
    }
  }
  this.lastExp = cnt; this.partial = false;
  let end = goal;
  if (!found) { if (best === start || cnt < maxN) return null; end = best; this.partial = true; }
  const nodes = [];
  for (let c = end; c !== -1; c = par[c]) nodes.push(c);
  nodes.reverse();
  const out = [nodes[0]];
  let anchor = 0;
  for (let i = 2; i < nodes.length; i++) {
    if (!this.nodeLOS(nodes[anchor], nodes[i])) { out.push(nodes[i - 1]); anchor = i - 1; }
  }
  if (nodes.length > 1) out.push(nodes[nodes.length - 1]);
  return out.map(k => [this.nodeX(k), this.nodeZ(k), sY[k]]);
};


/* ---------- рельеф ---------- */
// целочисленный хэш: одинаковый результат в любом браузере и на сервере
function ihash(x, z) { let h = (Math.imul(x, 374761393) + Math.imul(z, 668265263)) | 0; h = Math.imul(h ^ (h >>> 13), 1274126177); return ((h ^ (h >>> 16)) >>> 0) / 4294967296; }
function vnoise(x, z) {
  const xi = Math.floor(x), zi = Math.floor(z), fx = x - xi, fz = z - zi, u = fx * fx * (3 - 2 * fx), v = fz * fz * (3 - 2 * fz);
  const a = ihash(xi, zi), b = ihash(xi + 1, zi), c = ihash(xi, zi + 1), d = ihash(xi + 1, zi + 1);
  return a + (b - a) * u + (c - a) * v + (a - b - c + d) * u * v;
}
const TERRAIN_BOX = { mat: 'dirt', terrain: true };
World.TE = 352; World.THS = 2; // половина размера и шаг сетки высот
World.rawHeight = function (x, z) {
  return 4.2 * (vnoise(x / 58 + 3.1, z / 58 + 7.7) - 0.5) + 2.1 * (vnoise(x / 23 + 11.3, z / 23 + 1.9) - 0.5) + 0.5 * (vnoise(x / 8.3 + 5.5, z / 8.3 + 9.1) - 0.5)
    + 1.2 * Math.max(0, vnoise(x / 40 + 21.7, z / 40 + 4.3) - 0.62) * 6;
};
World.buildTerrain = function () {
  const E = this.TE, HS = this.THS, NG = Math.round(2 * E / HS) + 1;
  // зоны, где земля должна быть ровной: здания, дороги, двор, фронт спауна, ограда
  const rects = [];
  for (const b of this.buildings) rects.push([b.x0 - 0.6, b.x1 + 0.6, b.z0 - 0.6, b.z1 + 0.6]);
  for (const r of this.roads) rects.push([r.x0 - 1.5, r.x1 + 1.5, r.z0 - 1.5, r.z1 + 1.5]);
  for (const r of this.flat) rects.push(r);
  rects.push([this.spawnPlayer[0] - 9, this.spawnPlayer[0] + 9, this.spawnPlayer[1] - 9, this.spawnPlayer[1] + 9]);
  const T3 = this.T + 3, T0 = this.T - 3;
  rects.push([-T3, T3, -T3, -T0], [-T3, T3, T0, T3], [-T3, -T0, -T3, T3], [T0, T3, -T3, T3]);
  const DS = 1.5, DE = 128, DN = Math.round(2 * DE / DS) + 1, INF = 1e6;
  const df = new Float32Array(DN * DN).fill(INF);
  for (const r of rects) {
    const i0 = clamp(Math.floor((r[0] + DE) / DS), 0, DN - 1), i1 = clamp(Math.ceil((r[1] + DE) / DS), 0, DN - 1);
    const j0 = clamp(Math.floor((r[2] + DE) / DS), 0, DN - 1), j1 = clamp(Math.ceil((r[3] + DE) / DS), 0, DN - 1);
    for (let j = j0; j <= j1; j++) for (let i = i0; i <= i1; i++) df[j * DN + i] = 0;
  }
  // двухпроходное приближённое преобразование расстояния
  const w1 = DS, w2 = DS * 1.414;
  for (let j = 0; j < DN; j++) for (let i = 0; i < DN; i++) {
    let v = df[j * DN + i];
    if (i > 0) v = Math.min(v, df[j * DN + i - 1] + w1);
    if (j > 0) { v = Math.min(v, df[(j - 1) * DN + i] + w1); if (i > 0) v = Math.min(v, df[(j - 1) * DN + i - 1] + w2); if (i < DN - 1) v = Math.min(v, df[(j - 1) * DN + i + 1] + w2); }
    df[j * DN + i] = v;
  }
  for (let j = DN - 1; j >= 0; j--) for (let i = DN - 1; i >= 0; i--) {
    let v = df[j * DN + i];
    if (i < DN - 1) v = Math.min(v, df[j * DN + i + 1] + w1);
    if (j < DN - 1) { v = Math.min(v, df[(j + 1) * DN + i] + w1); if (i < DN - 1) v = Math.min(v, df[(j + 1) * DN + i + 1] + w2); if (i > 0) v = Math.min(v, df[(j + 1) * DN + i - 1] + w2); }
    df[j * DN + i] = v;
  }
  const maskAt = (x, z) => {
    if (x <= -DE || x >= DE || z <= -DE || z >= DE) return 1;
    const gx = (x + DE) / DS, gz = (z + DE) / DS, i = Math.floor(gx), j = Math.floor(gz), fx = gx - i, fz = gz - j;
    const d = df[j * DN + i] * (1 - fx) * (1 - fz) + df[j * DN + i + 1] * fx * (1 - fz) + df[(j + 1) * DN + i] * (1 - fx) * fz + df[(j + 1) * DN + i + 1] * fx * fz;
    return sm01((d - 3.5) / 15);
  };
  this.maskAt = maskAt;
  const H = new Float32Array(NG * NG); let hmax = 0;
  for (let j = 0; j < NG; j++) for (let i = 0; i < NG; i++) {
    const x = -E + i * HS, z = -E + j * HS, h = this.rawHeight(x, z) * maskAt(x, z);
    H[j * NG + i] = h; if (h > hmax) hmax = h;
  }
  this.hg = H; this.NG = NG; this.HMAX = hmax + 0.05;
  // мелкие предметы на открытой местности стоят на рельефе
  for (const b of this.boxes) {
    if (b.y0 !== 0 || b.terrainDone) continue;
    const cx = (b.x0 + b.x1) / 2, cz = (b.z0 + b.z1) / 2, hc = this.H(cx, cz);
    if (maskAt(cx, cz) < 0.001) continue;
    let lo = hc;
    for (const [x, z] of [[b.x0, b.z0], [b.x1, b.z0], [b.x0, b.z1], [b.x1, b.z1]]) lo = Math.min(lo, this.H(x, z));
    b.y1 += hc; b.y0 = lo - 0.2; b.terrainDone = true; b.baseY = hc;
  }
  for (const t of this.trees) t.y = this.H(t.x, t.z);
};
World.H = function (x, z) {
  const E = this.TE, HS = this.THS, NG = this.NG;
  if (!this.hg) return 0;
  let gx = (x + E) / HS, gz = (z + E) / HS;
  if (gx < 0) gx = 0; else if (gx > NG - 1.001) gx = NG - 1.001;
  if (gz < 0) gz = 0; else if (gz > NG - 1.001) gz = NG - 1.001;
  const i = gx | 0, j = gz | 0, fx = gx - i, fz = gz - j, h = this.hg, k = j * NG + i;
  return h[k] * (1 - fx) * (1 - fz) + h[k + 1] * fx * (1 - fz) + h[k + NG] * (1 - fx) * fz + h[k + NG + 1] * fx * fz;
};
World.Hn = function (x, z) {
  const e = 0.8, nx = this.H(x - e, z) - this.H(x + e, z), nz = this.H(x, z - e) - this.H(x, z + e), l = Math.hypot(nx, 2 * e, nz);
  return [nx / l, 2 * e / l, nz / l];
};
// пересечение луча с рельефом
World.rayTerrain = function (ox, oy, oz, dx, dy, dz, len) {
  if (!this.hg) return null;
  const top = this.HMAX;
  if (oy > top && dy >= 0) return null;
  if (oy > top && oy + dy * len > top) return null;
  let t = 0, f0 = oy - this.H(ox, oz);
  if (f0 < 0) return { t: 0.001, nx: 0, ny: 1, nz: 0 };
  const step = 1.0;
  while (t < len) {
    const t1 = Math.min(len, t + step), x = ox + dx * t1, y = oy + dy * t1, z = oz + dz * t1, f1 = y - this.H(x, z);
    if (f1 < 0) {
      let a = t, b = t1;
      for (let k = 0; k < 9; k++) { const m = (a + b) / 2; if (oy + dy * m - this.H(ox + dx * m, oz + dz * m) < 0) b = m; else a = m; }
      const hx = ox + dx * b, hz = oz + dz * b, n = this.Hn(hx, hz);
      return { t: b, nx: n[0], ny: n[1], nz: n[2] };
    }
    t = t1;
    if (y > top && dy >= 0) return null;
  }
  return null;
};

/* ---------- генерация карты ---------- */
const OPN = {
  door: { w: 1.5, y0: 0, y1: 2.2 }, wide: { w: 3.2, y0: 0, y1: 2.6 }, garage: { w: 4.2, y0: 0, y1: 3.4 },
  win: { w: 1.3, y0: 1.0, y1: 2.1 }, bigwin: { w: 2.8, y0: 0.9, y1: 2.5 }, hwin: { w: 1.6, y0: 3.8, y1: 5.2 },
};
function wall(ax, c, a0, a1, thk, h, mat, col, ops) {
  const segs = [];
  const list = (ops || []).slice().sort((p, q) => p.a - q.a);
  let cur = a0;
  const seg = (s, e, y0, y1) => {
    if (e - s < 0.02 || y1 - y0 < 0.02) return;
    const m = (s + e) / 2, L = e - s;
    if (ax === 'x') B(m, y0, c, L, y1 - y0, thk, mat, col); else B(c, y0, m, thk, y1 - y0, L, mat, col);
  };
  for (const o of list) {
    seg(cur, o.a, 0, h);
    seg(o.a, o.b, 0, o.y0);
    seg(o.a, o.b, o.y1, h);
    cur = o.b;
  }
  seg(cur, a1, 0, h);
}
function mkOps(arr, base) {
  return (arr || []).map(o => { const d = OPN[o.t]; return { a: base + o.o - d.w / 2, b: base + o.o + d.w / 2, y0: d.y0, y1: d.y1 }; });
}
function building(cx, cz, w, d, h, o) {
  const x0 = cx - w / 2, x1 = cx + w / 2, z0 = cz - d / 2, z1 = cz + d / 2, t = o.thk || 0.3;
  const mat = o.mat || 'brick', col = o.col === undefined ? 0xffffff : o.col;
  wall('x', z0, x0 - t / 2, x1 + t / 2, t, h, mat, col, mkOps(o.n, x0));
  wall('x', z1, x0 - t / 2, x1 + t / 2, t, h, mat, col, mkOps(o.s, x0));
  wall('z', x0, z0 + t / 2, z1 - t / 2, t, h, mat, col, mkOps(o.w, z0));
  wall('z', x1, z0 + t / 2, z1 - t / 2, t, h, mat, col, mkOps(o.e, z0));
  B(cx, h, cz, w + 0.7, 0.28, d + 0.7, 'roof', 0x6b6a66, { tex: 'roof' });
  B(cx, 0, cz, w - 0.2, 0.04, d - 0.2, 'concrete', o.floor || 0x8d8a84, { tex: o.floorTex || 'concrete' });
  for (const p of (o.parts || [])) {
    if (p.ax === 'x') wall('x', cz + p.c, cx + p.a0, cx + p.a1, 0.14, h, 'drywall', 0xd8d2c4, mkOps(p.ops, cx + p.a0));
    else wall('z', cx + p.c, cz + p.a0, cz + p.a1, 0.14, h, 'drywall', 0xd8d2c4, mkOps(p.ops, cz + p.a0));
  }
  const bd = { x0, x1, z0, z1, cx, cz, h };
  World.buildings.push(bd);
  const nl = Math.max(1, Math.round(w * d / 90));
  for (let i = 0; i < nl; i++) World.lights.push({ x: cx + (i - (nl - 1) / 2) * (w / nl), y: h - 0.4, z: cz, col: 0xffe2b0, int: 0.9, dist: Math.max(w, d) * 0.7 });
  if (o.props) o.props(bd);
  return bd;
}
const crate = (x, z, y, s, col) => B(x, y || 0, z, s || 1, s || 1, s || 1, 'wood', col || 0xb08a5a, { tex: 'crate' });
const barrel = (x, z, col) => B(x, 0, z, 0.62, 0.95, 0.62, 'metal', col || 0x44603f, { shape: 'cyl' });
const table = (x, z, w, d, h) => B(x, 0, z, w, h || 0.78, d, 'wood', 0x7a5c3a, { tex: 'wood' });
const shelf = (x, z, w, d, h) => B(x, 0, z, w, h || 2.2, d, 'metal', 0x5b6168, { shape: 'shelf' });
const sandbags = (x, z, rot) => rot ? B(x, 0, z, 0.8, 0.95, 4, 'sand', 0xb0a078, { tex: 'sand' }) : B(x, 0, z, 4, 0.95, 0.8, 'sand', 0xb0a078, { tex: 'sand' });
const barrier = (x, z, rot) => rot ? B(x, 0, z, 0.6, 1.05, 3.2, 'concrete', 0xb9b5ab) : B(x, 0, z, 3.2, 1.05, 0.6, 'concrete', 0xb9b5ab);
function car(x, z, rot, col) {
  const w = rot ? 1.9 : 4.5, d = rot ? 4.5 : 1.9, cw = rot ? 1.6 : 2.3, cd = rot ? 2.3 : 1.6;
  B(x, 0.28, z, w, 0.85, d, 'metal', col, { shape: 'car' });
  B(x + (rot ? 0 : -0.1), 1.13, z + (rot ? -0.1 : 0), cw, 0.62, cd, 'metal', col, { shape: 'cab' });
}
function tree(x, z, s, low) {
  s = s || srr(0.8, 1.4);
  World.trees.push({ x, z, s, low: !!low });
  B(x, 0, z, 0.5, 4 * s, 0.5, 'wood', 0x4a3524, { vis: false });
}

MAPS.poly = { name: 'Полигон', bound: 118, spawn: [0, 106], T: 120, pick: [9, 7], maxWP: 90, env: 'dusk', koth: [[-4, 7], [38, 18], [-50, -8], [20, -60]], gen: function () {
  srand(20261015);
  const bd = this.buildings;

  // ---- дороги (только визуал) ----
  this.roads.push({ x0: -118, x1: 118, z0: 4, z1: 11 }, { x0: -8, x1: -1, z0: -118, z1: 118 }, { x0: 42, x1: 49, z0: -118, z1: 4 });

  // ---- склад ----
  building(-62, -38, 34, 20, 6.5, {
    mat: 'concrete', col: 0xb9b6ae, floor: 0x777570,
    n: [{ o: 17, t: 'door' }, { o: 6, t: 'hwin' }, { o: 28, t: 'hwin' }],
    s: [{ o: 10, t: 'garage' }, { o: 27, t: 'door' }],
    w: [{ o: 10, t: 'garage' }],
    e: [{ o: 4, t: 'hwin' }, { o: 10, t: 'hwin' }, { o: 16, t: 'hwin' }, { o: 10, t: 'door' }],
    parts: [{ ax: 'z', c: 9, a0: -10, a1: -1.5, ops: [{ o: 4, t: 'door' }] }, { ax: 'x', c: -1.5, a0: 9, a1: 17, ops: [{ o: 3, t: 'door' }] }],
    props(b) {
      for (let r = 0; r < 3; r++) for (let k = 0; k < 3; k++) shelf(b.cx - 11 + k * 5.5, b.cz - 5.5 + r * 3.2, 1.2, 6.5, 2.4);
      crate(b.cx + 3, b.cz + 6, 0, 1.2); crate(b.cx + 4.4, b.cz + 6, 0, 1.2); crate(b.cx + 3.7, b.cz + 6, 1.2, 1.1);
      crate(b.cx - 13, b.cz + 6.5, 0, 1.3); barrel(b.cx + 12, b.cz - 6); barrel(b.cx + 12.8, b.cz - 6.5); barrel(b.cx + 12.3, b.cz - 7.3);
      table(b.cx + 13, b.cz + 6, 2, 1, 0.8);
    },
  });

  // ---- жилой дом ----
  building(35, -38, 22, 12, 3.4, {
    mat: 'brick', col: 0xc9a58f,
    n: [{ o: 5, t: 'win' }, { o: 11, t: 'door' }, { o: 17, t: 'win' }],
    s: [{ o: 4, t: 'door' }, { o: 9, t: 'win' }, { o: 15, t: 'win' }, { o: 19.5, t: 'win' }],
    w: [{ o: 6, t: 'win' }], e: [{ o: 6, t: 'door' }],
    parts: [
      { ax: 'z', c: -3.6, a0: -6, a1: 6, ops: [{ o: 6, t: 'door' }] },
      { ax: 'z', c: 3.8, a0: -6, a1: 6, ops: [{ o: 6.2, t: 'door' }] },
      { ax: 'x', c: 0, a0: -11, a1: -3.6, ops: [{ o: 3.5, t: 'door' }] },
      { ax: 'x', c: 0, a0: 3.8, a1: 11, ops: [{ o: 3.5, t: 'door' }] },
    ],
    props(b) { table(b.cx - 7, b.cz - 3, 1.8, 0.9); table(b.cx + 7, b.cz + 3.5, 1.6, 0.9); table(b.cx, b.cz + 3.5, 2, 1, 0.5); crate(b.cx + 8, b.cz - 3.5, 0, 0.8); },
  });

  // ---- магазин ----
  building(-25, 40, 14, 10, 3.6, {
    mat: 'plaster', col: 0xd6cfbd, floorTex: 'tile', floor: 0xa59f93,
    s: [{ o: 4, t: 'bigwin' }, { o: 9, t: 'door' }, { o: 12.2, t: 'win' }],
    n: [{ o: 10, t: 'door' }], w: [{ o: 5, t: 'win' }], e: [{ o: 5, t: 'win' }],
    props(b) { shelf(b.cx - 2, b.cz - 1.5, 5, 0.7, 1.7); shelf(b.cx - 2, b.cz + 0.8, 5, 0.7, 1.7); table(b.cx + 4, b.cz + 3, 3.5, 0.8, 1.05); },
  });

  // ---- гараж ----
  building(-85, 45, 18, 11, 4, {
    mat: 'concrete', col: 0xa8a49b, floor: 0x6f6d68,
    e: [{ o: 5.5, t: 'garage' }, { o: 9.5, t: 'door' }], w: [{ o: 4, t: 'door' }],
    n: [{ o: 4, t: 'hwin' }, { o: 9, t: 'hwin' }, { o: 14, t: 'hwin' }], s: [{ o: 9, t: 'door' }],
    props(b) { car(b.cx - 3, b.cz - 2.5, false, 0x6d7c88); barrel(b.cx + 6.5, b.cz + 4); crate(b.cx - 7.5, b.cz + 4, 0, 1.1); table(b.cx - 7, b.cz - 4, 2, 0.9, 0.9); },
  });

  // ---- офисный блок ----
  building(50, 38, 26, 14, 3.6, {
    mat: 'brick', col: 0xb88f7c,
    n: [{ o: 6, t: 'win' }, { o: 13, t: 'door' }, { o: 20, t: 'win' }],
    s: [{ o: 6, t: 'win' }, { o: 13, t: 'door' }, { o: 20, t: 'win' }],
    w: [{ o: 7, t: 'door' }], e: [{ o: 7, t: 'win' }],
    parts: [
      { ax: 'x', c: -1.8, a0: -13, a1: 13, ops: [{ o: 3, t: 'door' }, { o: 9, t: 'door' }, { o: 16, t: 'door' }, { o: 22, t: 'door' }] },
      { ax: 'x', c: 1.8, a0: -13, a1: 13, ops: [{ o: 3, t: 'door' }, { o: 9, t: 'door' }, { o: 16, t: 'door' }, { o: 22, t: 'door' }] },
      { ax: 'z', c: -6.5, a0: -7, a1: -1.8 }, { ax: 'z', c: 0, a0: -7, a1: -1.8 }, { ax: 'z', c: 6.5, a0: -7, a1: -1.8 },
      { ax: 'z', c: -6.5, a0: 1.8, a1: 7 }, { ax: 'z', c: 0, a0: 1.8, a1: 7 }, { ax: 'z', c: 6.5, a0: 1.8, a1: 7 },
    ],
    props(b) { for (const dx of [-9.5, -3, 3.5, 9.5]) { table(b.cx + dx, b.cz - 4.8, 1.6, 0.8); table(b.cx + dx, b.cz + 4.8, 1.6, 0.8); } },
  });

  // ---- казарма ----
  building(82, -2, 24, 9, 3.2, {
    mat: 'plaster', col: 0xc3bfa8,
    n: [{ o: 6, t: 'win' }, { o: 12, t: 'door' }, { o: 18, t: 'win' }], s: [{ o: 6, t: 'win' }, { o: 12, t: 'door' }, { o: 18, t: 'win' }],
    w: [{ o: 4.5, t: 'door' }], e: [{ o: 4.5, t: 'door' }],
    props(b) { for (let i = 0; i < 4; i++) { B(b.cx - 8.5 + i * 3, 0, b.cz - 3.2, 0.9, 0.5, 2.0, 'wood', 0x5a6350); B(b.cx - 8.5 + i * 3, 0, b.cz + 3.2, 0.9, 0.5, 2.0, 'wood', 0x5a6350); } },
  });

  // ---- насосная ----
  building(22, 82, 7, 5.5, 3, { mat: 'concrete', col: 0xaaa69c, s: [{ o: 3.5, t: 'door' }], n: [{ o: 3.5, t: 'win' }], e: [{ o: 2.7, t: 'win' }], props(b) { barrel(b.cx, b.cz, 0x7a3b30); } });

  // ---- руины ----
  wall('x', -78, -22, -9, 0.4, 2.8, 'brick', 0xa27c68, [{ a: -17, b: -15.2, y0: 0, y1: 2.2 }]);
  wall('z', -22, -90, -78, 0.4, 3.0, 'brick', 0xa27c68, [{ a: -85, b: -83.5, y0: 0.9, y1: 2.1 }]);
  wall('x', -90, -22, -12, 0.4, 1.7, 'brick', 0xa27c68);
  wall('z', -12, -90, -80, 0.4, 2.2, 'brick', 0xa27c68);
  B(-18, 0, -84, 2.4, 0.8, 1.6, 'brick', 0x9a7662); B(-14.5, 0, -86, 1.5, 1.3, 1.8, 'brick', 0x8e6c5a);
  World.buildings.push({ x0: -22, x1: -12, z0: -90, z1: -78, cx: -17, cz: -84, h: 0, ruin: true });

  // ---- контейнерный двор ----
  const cols = [0x8a3b32, 0x2f5d73, 0x7a6a2e, 0x3a5e3a, 0x6b5a4a, 0x4d4f6b];
  for (let r = 0; r < 3; r++) for (let k = 0; k < 4; k++) {
    if ((r * 4 + k) % 5 === 3) continue;
    const x = -97 + k * 8.4, z = -88 + r * 6.2 + (k % 2 ? 0.8 : 0);
    const c = cols[(r * 3 + k * 2) % cols.length];
    B(x, 0, z, 6.1, 2.6, 2.45, 'metal', c, { shape: 'container', tex: 'container' });
    if ((r + k) % 3 === 0) B(x, 2.6, z, 6.1, 2.6, 2.45, 'metal', cols[(r + k + 2) % cols.length], { shape: 'container', tex: 'container' });
  }

  // ---- укрытия на открытой местности ----
  const occ = [];
  const inside = (x, z, m) => this.buildings.some(b => x > b.x0 - m && x < b.x1 + m && z > b.z0 - m && z < b.z1 + m);
  const inYard = (x, z) => x > -104 && x < -60 && z > -96 && z < -64;
  const free = (x, z, r) => !inside(x, z, r + 3) && !inYard(x, z) && Math.hypot(x - this.spawnPlayer[0], z - this.spawnPlayer[1]) > 9 && occ.every(o => Math.hypot(o[0] - x, o[1] - z) > o[2] + r);
  const spot = (r) => { for (let k = 0; k < 40; k++) { const x = srr(-108, 108), z = srr(-108, 108); if (free(x, z, r)) { occ.push([x, z, r]); return [x, z]; } } return null; };
  for (let i = 0; i < 16; i++) { const p = spot(1.6); if (p) { const s = srnd() < 0.3 ? 1.3 : 1; crate(p[0], p[1], 0, s); if (srnd() < 0.5) crate(p[0] + 1.1, p[1] + 0.2, 0, 1); if (srnd() < 0.3) crate(p[0] + 0.4, p[1], s, 0.9); } }
  for (let i = 0; i < 10; i++) { const p = spot(1); if (p) { barrel(p[0], p[1], pick2([0x44603f, 0x7a3b30, 0x2f4f6b])); if (srnd() < 0.6) barrel(p[0] + 0.8, p[1] + 0.3, 0x44603f); } }
  for (let i = 0; i < 14; i++) { const p = spot(2.2); if (p) barrier(p[0], p[1], srnd() < 0.5); }
  for (let i = 0; i < 8; i++) { const p = spot(2.4); if (p) sandbags(p[0], p[1], srnd() < 0.5); }
  const ccols = [0x6d7c88, 0x7a3b30, 0x57595c, 0x3f5c48, 0x8a7d5a];
  for (let i = 0; i < 6; i++) { const p = spot(3); if (p) car(p[0], p[1], srnd() < 0.5, ccols[i % ccols.length]); }
  // деревянные заборы
  for (let i = 0; i < 4; i++) { const p = spot(4); if (p) { if (srnd() < 0.5) B(p[0], 0, p[1], 8, 1.8, 0.06, 'wood', 0x7d6244, { tex: 'wood' }); else B(p[0], 0, p[1], 0.06, 1.8, 8, 'wood', 0x7d6244, { tex: 'wood' }); } }
  // камни
  for (let i = 0; i < 22; i++) { const p = spot(1); if (p) { const s = srr(0.7, 1.8); B(p[0], 0, p[1], s * 1.3, s * 0.85, s, 'concrete', 0x77746c, { shape: 'rock' }); } }

  // ---- деревья ----
  for (let i = 0; i < 90; i++) {
    const x = srr(-112, 112), z = srr(-112, 112);
    if (inside(x, z, 5) || inYard(x, z) || Math.hypot(x - this.spawnPlayer[0], z - this.spawnPlayer[1]) < 10) continue;
    if (this.roads.some(r => x > r.x0 - 3 && x < r.x1 + 3 && z > r.z0 - 3 && z < r.z1 + 3)) continue;
    if (occ.some(o => Math.hypot(o[0] - x, o[1] - z) < o[2] + 0.8)) continue;
    tree(x, z);
  }
  for (let i = 0; i < 150; i++) {
    const a = srnd() * 4, t = srr(-114, 114), off = srr(104, 116);
    const p = a < 1 ? [t, -off] : a < 2 ? [t, off] : a < 3 ? [-off, t] : [off, t];
    if (this.roads.some(r => p[0] > r.x0 - 3 && p[0] < r.x1 + 3 && p[1] > r.z0 - 3 && p[1] < r.z1 + 3)) continue;
    tree(p[0], p[1], srr(1.0, 1.7));
  }
  // ограда периметра
  const T = 120;
  B(0, 0, -T, 244, 5, 1, 'concrete', 0x8c897f, { vis: false }); B(0, 0, T, 244, 5, 1, 'concrete', 0x8c897f, { vis: false });
  B(-T, 0, 0, 1, 5, 244, 'concrete', 0x8c897f, { vis: false }); B(T, 0, 0, 1, 5, 244, 'concrete', 0x8c897f, { vis: false });

  this.flat.push([-104, -60, -96, -64]);
}};
function pick2(a) { return a[Math.floor(srnd() * a.length)]; }

World.flood = function () {
  const n = this.nn, N = this.sY.length, reach = new Uint8Array(N);
  const sp = this.spawnPlayer, s = this.nearestNode(sp[0], sp[1], this.H(sp[0], sp[1]));
  const q = [s]; reach[s] = 1;
  const DI = [1, -1, 0, 0], DJ = [0, 0, 1, -1];
  for (let h = 0; h < q.length; h++) {
    const c = q[h];
    for (let k = 0; k < 4; k++) { const nn = this.adj[c * 8 + k]; if (nn >= 0 && !reach[nn]) { reach[nn] = 1; q.push(nn); } }
  }
  this.reach = reach;
  const reachNode = (x, z, y, tol) => { const k = this.surfAt(x, z, y, tol); return k >= 0 && reach[k] ? k : -1; };
  this.reachAt = (x, z, y) => reachNode(x, z, y === undefined ? this.H(x, z) : y, 0.9) >= 0;
  const wpOk = (x, z, y, sp_) => this.waypoints.every(w => Math.hypot(w[0] - x, w[1] - z) + Math.abs(w[2] - y) * 3 > sp_);
  srand(777);
  const R_ = this.bound - 8, maxWP = this.maxWP || 90;
  for (let t = 0; t < 8000 && this.waypoints.length < maxWP; t++) {
    const x = srr(-R_, R_), z = srr(-R_, R_), c = this.cellOf(z) * n + this.cellOf(x);
    const opts = [];
    for (let k = this.sStart[c]; k < this.sStart[c + 1]; k++) if (reach[k]) opts.push(k);
    if (!opts.length) continue;
    const k = opts[Math.floor(srnd() * opts.length)], y = this.sY[k];
    if (wpOk(x, z, y, 9)) this.waypoints.push([x, z, y]);
  }
  for (const b of this.buildings) {
    if (b.ruin) continue;
    const lv = b.levels || 1;
    for (let l = 0; l < lv; l++) {
      let got = 0;
      for (let t = 0; t < 80 && got < (b.wpPer || 1); t++) {
        const x = srr(b.x0 + 1.5, b.x1 - 1.5), z = srr(b.z0 + 1.5, b.z1 - 1.5), y0 = l * this.LH;
        const k = reachNode(x, z, y0, 0.6);
        if (k >= 0 && wpOk(x, z, this.sY[k], 5)) { this.waypoints.push([x, z, this.sY[k]]); got++; }
      }
    }
  }
  for (const h of this.hintWP) { const k = reachNode(h[0], h[1], h[2], 0.6); if (k >= 0) this.waypoints.push([h[0], h[1], this.sY[k]]); }
  this.botSpawns = this.waypoints.slice();
};

World.placePickups = function () {
  srand(4242);
  let med = 0, ammo = 0;
  const [nm, na] = this.pickN || [9, 7];
  const bs = this.buildings.filter(b => !b.ruin);
  for (let k = 0; k < 1500 && (med < nm || ammo < na); k++) {
    const b = bs[k % bs.length], l = Math.floor(srnd() * (b.levels || 1));
    const x = srr(b.x0 + 1, b.x1 - 1), z = srr(b.z0 + 1, b.z1 - 1);
    const nd = this.surfAt(x, z, l * this.LH, 0.6);
    if (nd < 0 || !this.reach[nd]) continue;
    const y = this.sY[nd];
    if (this.pickups.some(p => Math.hypot(p.x - x, p.z - z) + Math.abs(p.y - y) * 3 < 4)) continue;
    const type = (med < nm && (med <= ammo || ammo >= na)) ? 'med' : 'ammo';
    if (type === 'med') med++; else ammo++;
    this.pickups.push({ type, x, z, y, taken: false });
  }
};

if (typeof module !== 'undefined') module.exports = { World, MATS };

/* --- 12_dorms.js --- */
/* ===== Карта «Общага»: два общежития (3 и 2 этажа), двор, лес, дорога ===== */
const DLH = 3.2, SLAB = 0.25, STEPN = 10, RISE = 0.16;

// проём по центру c (абсолютная координата вдоль стены)
function opn(c, t) { const d = OPN[t]; return { a: c - d.w / 2, b: c + d.w / 2, y0: d.y0, y1: d.y1 }; }
function opw(a, b, y0, y1) { return { a, b, y0, y1 }; }

// стена с проёмами на этаже y; lo/hi — вертикальный диапазон внутри стены (для двухцветной покраски)
function wallY(ax, c, a0, a1, thk, y, h, mat, col, ops, tex, lo, hi) {
  lo = lo || 0; if (hi === undefined) hi = h;
  const list = (ops || []).slice().sort((p, q) => p.a - q.a);
  const o = tex ? { tex } : null;
  const seg = (s, e, z0, z1) => {
    z0 = Math.max(z0, lo); z1 = Math.min(z1, hi);
    if (e - s < 0.02 || z1 - z0 < 0.02) return;
    const m = (s + e) / 2, L = e - s;
    if (ax === 'x') B(m, y + z0, c, L, z1 - z0, thk, mat, col, o); else B(c, y + z0, m, thk, z1 - z0, L, mat, col, o);
  };
  let cur = a0;
  for (const p of list) { seg(cur, p.a, 0, h); seg(p.a, p.b, 0, p.y0); seg(p.a, p.b, p.y1, h); cur = p.b; }
  seg(cur, a1, 0, h);
}
// коридорная стена: зелёная масляная панель снизу, грязно-белый верх
function paintWall(ax, c, a0, a1, thk, y, h, ops) {
  wallY(ax, c, a0, a1, thk + 0.03, y, h, 'plaster', 0xffffff, ops, 'paintg', 0, 1.45);
  wallY(ax, c, a0, a1, thk, y, h, 'plaster', 0xffffff, ops, 'paintw', 1.45, h);
}
function sign(ax, dir, x, y, z, txt, w, h, kind) { World.signs.push({ ax, dir, x, y, z, txt, w: w || 0.42, h: h || 0.2, kind: kind || 0 }); }
function slabAt(f, x0, x1, z0, z1, tex, col) {
  const y = f * DLH, th = f === 0 ? 0.3 : SLAB, top = f === 0 ? 0.03 : y;
  B((x0 + x1) / 2, top - th, (z0 + z1) / 2, x1 - x0, th, z1 - z0, 'concrete', 0xb4b0a6, { tex: 'plaster' });
  B((x0 + x1) / 2, top, (z0 + z1) / 2, x1 - x0, 0.012, z1 - z0, 'concrete', col === undefined ? 0xffffff : col, { tex: tex || 'terrazzo' });
}
// система координат помещения: u вдоль x (от вершины vx в сторону away), v от стороны двери zd к дальней стене zf
function frm(vx, away, zd, zf) { return { vx, away, zd, dz: Math.sign(zf - zd) }; }
function Bf(fr, u, v, wu, h, dv, y, mat, col, opt) { return B(fr.vx + fr.away * u, y, fr.zd + fr.dz * v, wu, h, dv, mat, col, opt); }
function Df(fr, u, v, wu, h, dv, y, mat, col, opt) { return D(fr.vx + fr.away * u, y, fr.zd + fr.dz * v, wu, h, dv, mat, col, opt); }

/* ---------- декор без столкновений: рамы, наличники, плинтусы, лампы ---------- */
const PAINT = 0xe6e2d6, WOODD = 0x4b3b2c;
// оконная рама в проёме наружной стены; c — ось стены, sg — куда «внутрь здания» (+1/−1), op — проём {a,b,y0,y1}, y — отметка этажа
function winFrame(ax, c, op, y, sg) {
  const w = op.b - op.a, h = op.y1 - op.y0, th = 0.06, dt = 0.1, d0 = sg * 0.02 - dt / 2, d1 = sg * 0.02 + dt / 2;
  const bx = (u0, u1, v0, v1, e0, e1, col) => {
    if (ax === 'x') D((u0 + u1) / 2, y + v0, c + (e0 + e1) / 2, u1 - u0, v1 - v0, Math.abs(e1 - e0), 'plaster', col, { tex: 'paintw' });
    else D(c + (e0 + e1) / 2, y + v0, (u0 + u1) / 2, Math.abs(e1 - e0), v1 - v0, u1 - u0, 'plaster', col, { tex: 'paintw' });
  };
  bx(op.a, op.a + th, op.y0, op.y1, d0, d1, PAINT); bx(op.b - th, op.b, op.y0, op.y1, d0, d1, PAINT);
  bx(op.a, op.b, op.y0, op.y0 + th, d0, d1, PAINT); bx(op.a, op.b, op.y1 - th, op.y1, d0, d1, PAINT);
  const nm = w >= 1.4 ? 2 : w >= 0.85 ? 1 : 0;
  for (let k = 1; k <= nm; k++) { const m = op.a + w * k / (nm + 1); bx(m - 0.025, m + 0.025, op.y0, op.y1, d0 + 0.02, d1 - 0.02, PAINT); }
  if (h >= 0.95) { const ty = op.y0 + h * 0.68; bx(op.a, op.b, ty, ty + 0.04, d0 + 0.02, d1 - 0.02, PAINT); }
  // подоконник внутри и отлив снаружи
  const fi = sg * 0.15, fo = -sg * 0.15;
  bx(op.a - 0.05, op.b + 0.05, op.y0 - 0.045, op.y0, Math.min(fi, fi + sg * 0.1), Math.max(fi, fi + sg * 0.1), 0xd8d4c8);
  bx(op.a - 0.04, op.b + 0.04, op.y0 - 0.04, op.y0 + 0.01, Math.min(fo, fo - sg * 0.07), Math.max(fo, fo - sg * 0.07), 0x9a978d);
}
// наличник двери в перегородке: ось стены c, проём [a,b], высота h, толщина стены thk
function doorFrame(ax, c, a, b, h, thk, y) {
  const j = 0.07, e = thk + 0.03;
  const bx = (u0, u1, v0, v1) => { if (ax === 'x') D((u0 + u1) / 2, y + v0, c, u1 - u0, v1 - v0, e, 'wood', WOODD, { tex: 'wood' }); else D(c, y + v0, (u0 + u1) / 2, e, v1 - v0, u1 - u0, 'wood', WOODD, { tex: 'wood' }); };
  bx(a, a + j, 0, h); bx(b - j, b, 0, h); bx(a, b, h - j, h);
}
// плинтус вдоль стены помещения: от u0 до u1 (в системе помещения) на расстоянии v от стороны двери; side: 'v' — вдоль v при заданном u
function skirtV(fr, u, v0, v1, y) { Df(fr, u, (v0 + v1) / 2, 0.025, 0.1, Math.abs(v1 - v0), y, 'wood', 0x3d3228, { tex: 'wood' }); }
function skirtU(fr, v, u0, u1, y) { Df(fr, (u0 + u1) / 2, v, Math.abs(u1 - u0), 0.1, 0.025, y, 'wood', 0x3d3228, { tex: 'wood' }); }
function lampAt(x, y, z, big) { const s = big ? 0.5 : 0.32; D(x, y, z, s, 0.06, big ? 0.16 : s, 'plaster', 0xf0ecdc, { tex: 'paintw' }); }

/* ---------- помещения: зоны, куда мебель не ставится, и контроль пересечений ---------- */
function mkRoom(fr, W, Dp, y, f) { return { fr, W, D: Dp, y, f, keep: [], occ: [], dropped: 0 }; }
function rmHit(r, u, v, wu, dv, gap) {
  for (const k of r.keep) if (Math.abs(u - k.u) < (wu + k.wu) / 2 && Math.abs(v - k.v) < (dv + k.dv) / 2) return true;
  for (const o of r.occ) if (Math.abs(u - o.u) < (wu + o.wu) / 2 + gap && Math.abs(v - o.v) < (dv + o.dv) / 2 + gap) return true;
  return false;
}
// поставить коробку (центр u,v; размеры по x, y, z), если она в пределах комнаты, не в зоне прохода и не на другой мебели
function rmPut(r, u, v, wu, h, dv, mat, col, opt, y0) {
  if (u - wu / 2 < -0.001 || u + wu / 2 > r.W + 0.001 || v - dv / 2 < -0.001 || v + dv / 2 > r.D + 0.001 || rmHit(r, u, v, wu, dv, 0.03)) { r.dropped++; return null; }
  r.occ.push({ u, v, wu, dv });
  return Bf(r.fr, u, v, wu, h, dv, r.y + (y0 || 0), mat, col, opt);
}
const fcU = (r, d) => (r.fr.away * d > 0 ? '+x' : '-x'); // грань, смотрящая в сторону d по оси u
const fcV = (r, d) => (r.fr.dz * d > 0 ? '+z' : '-z');   // то же по оси v
const BEDC = [0x9aa886, 0xa89078, 0x7f93a6, 0xb09a68, 0x9a8190];
const PICK = a => a[Math.floor(srnd() * a.length) % a.length];
// предметы вдоль боковой стены: dep — глубина от стены, len — длина вдоль стены
const ITEM = {
  bed: { dep: 0.95, len: 2.05, mk(r, u, v) { return rmPut(r, u, v, 0.95, 0.62, 2.05, 'metal', PICK(BEDC), { shape: 'bed', head: r.fr.dz }); } },
  ward: { dep: 0.58, len: 1.15, mk(r, u, v) { return rmPut(r, u, v, 0.58, 1.95, 1.15, 'wood', PICK([0xb09470, 0x9a7e5c, 0xa88a64]), { shape: 'wardrobe', tex: 'wood' }); } },
  night: { dep: 0.42, len: 0.42, mk(r, u, v) { const b = rmPut(r, u, v, 0.42, 0.55, 0.42, 'wood', 0x6a5236, { tex: 'wood' }); if (b && srnd() < 0.6) Df(r.fr, u, v, 0.1, 0.28, 0.1, r.y + 0.55, 'metal', 0x2a2a2a); return b; } },
  desk: {
    dep: 0.65, len: 1.3, mk(r, u, v, side) {
      const b = rmPut(r, u, v, 0.65, 0.74, 1.3, 'wood', 0x7a5c3a, { shape: 'table' }); if (!b) return null;
      rmPut(r, u + (side < 0 ? 1 : -1) * (0.65 / 2 + 0.3), v + (srnd() - 0.5) * 0.4, 0.4, 0.42, 0.4, 'wood', 0x5a4630, { shape: 'stool' });
      Df(r.fr, u, v - 0.3, 0.3, 0.012, 0.22, r.y + 0.74, 'plaster', 0xe8e4d8); if (srnd() < 0.5) Df(r.fr, u + (side < 0 ? -0.15 : 0.15), v + 0.4, 0.12, 0.3, 0.12, r.y + 0.74, 'metal', 0x2a2a2a);
      return b;
    },
  },
  shelf: { dep: 0.32, len: 0.95, mk(r, u, v, side) { return rmPut(r, u, v, 0.32, 1.75, 0.95, 'wood', 0x6a5236, { shape: 'bookcase', face: fcU(r, side < 0 ? 1 : -1) }); } },
  fridge: { dep: 0.6, len: 0.62, mk(r, u, v, side) { return rmPut(r, u, v, 0.6, 1.25, 0.62, 'metal', 0xd8d6cf, { shape: 'fridge', face: fcU(r, side < 0 ? 1 : -1) }); } },
  sofa: { dep: 0.85, len: 1.9, mk(r, u, v, side) { return rmPut(r, u, v, 0.85, 0.82, 1.9, 'plaster', PICK([0x6a5a48, 0x56604a, 0x5a4a52, 0x4a5662]), { shape: 'sofa', face: fcU(r, side < 0 ? 1 : -1) }); } },
  tv: { dep: 0.45, len: 0.9, mk(r, u, v, side) { const b = rmPut(r, u, v, 0.45, 0.55, 0.9, 'wood', 0x6a5236, { tex: 'wood' }); if (b) Df(r.fr, u + (side < 0 ? 0.03 : -0.03), v, 0.36, 0.4, 0.62, r.y + 0.55, 'metal', 0x14161a); return b; } },
  rack: { dep: 0.5, len: 1.0, mk(r, u, v) { return rmPut(r, u, v, 0.5, 2.0, 1.0, 'metal', 0x5b6168, { shape: 'shelf' }); } },
  crates: { dep: 0.8, len: 0.8, mk(r, u, v) { const b = rmPut(r, u, v, 0.8, 0.8, 0.8, 'wood', 0xb08a5a, { tex: 'crate' }); if (b && srnd() < 0.7) Bf(r.fr, u, v, 0.7, 0.7, 0.7, r.y + 0.8, 'wood', 0xa0805a, { tex: 'crate' }); return b; } },
  barrel: { dep: 0.62, len: 0.62, mk(r, u, v) { return rmPut(r, u, v, 0.62, 0.95, 0.62, 'metal', PICK([0x44603f, 0x56504a, 0x3f4f6a]), { shape: 'cyl' }); } },
};
const TPL = [
  ['bed', 'night', 'ward'], ['bed', 'bed'], ['bed', 'desk', 'shelf'], ['bed', 'sofa'], ['desk', 'bed', 'ward'], ['bed', 'fridge', 'ward'], ['night', 'bed', 'shelf', 'ward'], ['sofa', 'tv', 'ward'], ['bed', 'night', 'desk'],
];
// ряд предметов вдоль боковой стены от дальней (оконной) стены к двери; числа в списке — дополнительные промежутки
function sideRun(r, side, list) {
  let ve = r.D - 0.1;
  for (const nm of list) {
    if (typeof nm === 'number') { ve -= nm; continue; }
    const it = ITEM[nm]; if (!it) continue;
    const v = ve - it.len / 2;
    if (v - it.len / 2 < 0.1) break;
    const u = side < 0 ? 0.06 + it.dep / 2 : r.W - 0.06 - it.dep / 2;
    it.mk(r, u, v, side);
    ve -= it.len + 0.06;
  }
}
// плакаты, шторы, лампа, плинтус — только визуал
function roomDeco(r, style, exitU) {
  const { fr, W, D: Dp } = r, y = r.y;
  const far = style !== 4 || exitU === undefined;
  skirtV(fr, 0.0125, 0.0, Dp, y); skirtV(fr, W - 0.0125, 0.0, Dp, y);
  if (style !== 4) skirtU(fr, Dp - 0.0125, 0.0, W, y);
  else { skirtU(fr, Dp - 0.0125, 0.0, Math.max(0, exitU - 0.8), y); skirtU(fr, Dp - 0.0125, Math.min(W, exitU + 0.8), W, y); }
  // входная стена: плинтус по обе стороны проёма
  skirtU(fr, 0.0125, 0.0, W / 2 - 0.8, y); skirtU(fr, 0.0125, W / 2 + 0.8, W, y);
  if (style !== 2 || srnd() < 0.5) lampAt(fr.vx + fr.away * W / 2, y + DLH - SLAB - 0.06 - (r.f === 0 ? 0.03 : 0), fr.zd + fr.dz * Dp * 0.5, false);
  if (style === 4) return;
  // шторы у окна
  if (srnd() < 0.55) {
    const col = PICK([0x7a6a58, 0x5a6a52, 0x6a5a62, 0x8a8068]);
    for (const s of [-1, 1]) Df(fr, W / 2 + s * 1.0, Dp - 0.06, 0.34, 1.55, 0.05, y + 0.85, 'plaster', col, { tex: 'wallpaper' });
  }
  // плакат или доска на боковой стене
  if (srnd() < 0.5) {
    const side = srnd() < 0.5 ? 0 : 1, v = 1.4 + srnd() * (Dp - 3), cl = PICK([0xa84a3a, 0x3a6a8a, 0xc8b060, 0x4a7a4a, 0xd8d4c4]);
    Df(fr, side ? W - 0.012 : 0.012, v, 0.012, 0.7, 0.5, y + 1.25, 'plaster', cl, { tex: 'paintw' });
  }
}
// жилая комната. style: 0 обычная, 1 разгром, 2 почти пустая, 3 кладовка, 4 выход на пожарную лестницу
function furnishRoom(r, style, exitU) {
  const { W, D: Dp, fr } = r;
  r.keep.push({ u: style === 4 ? exitU : W / 2, v: Dp / 2, wu: style === 4 ? 2.2 : 1.5, dv: Dp }); // сквозной проход от двери до окна
  r.keep.push({ u: W / 2, v: 0.9, wu: 2.5, dv: 1.8 });                                               // площадка у входа
  if (style === 4) { r.keep.push({ u: (exitU + W / 2) / 2, v: Dp / 2, wu: Math.abs(exitU - W / 2) + 2.0, dv: Dp }); roomDeco(r, 4, exitU); return; }
  Bf(fr, W / 2, Dp - 0.07, 1.0, 0.65, 0.12, r.y + 0.22, 'metal', 0xcfc9b4, { shape: 'radiator' });
  if (style === 3) { // кладовка: два коротких стеллажа у одной стены, ящики и бочки в углу, проход свободен
    const side = srnd() < 0.5 ? -1 : 1;
    sideRun(r, side, ['rack', 0.9, 'rack']);
    sideRun(r, -side, ['crates', 0.3, 'crates', 0.5, 'barrel']);
  } else if (style === 2) {
    sideRun(r, srnd() < 0.5 ? -1 : 1, PICK([['bed', 'night'], ['desk'], ['sofa'], ['bed']]));
    if (srnd() < 0.5) sideRun(r, srnd() < 0.5 ? -1 : 1, ['ward']);
  } else {
    let L = PICK(TPL), R = PICK(TPL);
    if (!L.includes('bed') && !R.includes('bed')) R = TPL[0];
    sideRun(r, -1, L); sideRun(r, 1, R);
    if (style === 1) { // разгром: часть мебели осталась, на полу обломки и опрокинутый шкаф
      rmPut(r, W / 2 + (srnd() < 0.5 ? -1 : 1) * 1.55, 2.2 + srnd() * (Dp - 4.4), 0.6, 0.58, 1.9, 'wood', 0x5a4a38, { tex: 'wood' });
      const nj = 5 + Math.floor(srnd() * 5);
      for (let k = 0; k < nj; k++) { const s = 0.3 + srnd() * 0.5; rmPut(r, 0.3 + srnd() * (W - 0.6), 0.8 + srnd() * (Dp - 1.2), s * 1.4, 0.16 + srnd() * 0.18, s, 'wood', [0x6a5a48, 0x4a4a46, 0x7a6e5a, 0x3f4a40][k % 4], { shape: 'junk' }); }
    }
  }
  roomDeco(r, style);
}

/* ---------- холл: сквозной проход шириной 3 м свободен, мебель только у боковых стен ---------- */
function hallRoom(r) {
  const { fr, W, D: Dp, y } = r;
  r.keep.push({ u: W / 2, v: Dp / 2, wu: 3.3, dv: Dp });
  // вахта слева, шкафчики и скамья справа
  rmPut(r, 0.06 + 0.35, 3.1, 0.7, 1.05, 1.8, 'wood', 0x5a4632, { shape: 'table' });
  rmPut(r, 0.06 + 0.9, 3.1, 0.4, 0.42, 0.4, 'wood', 0x4a3a2a, { shape: 'stool' });
  rmPut(r, W - 0.06 - 0.22, 1.9, 0.44, 1.85, 1.7, 'metal', 0x4f5a52, { shape: 'locker', face: fcU(r, -1) });
  rmPut(r, W - 0.06 - 0.2, 3.9, 0.4, 0.42, 1.5, 'wood', 0x6a5236, { shape: 'bench' });
  rmPut(r, 0.06 + 0.3, 5.0, 0.6, 0.5, 0.6, 'wood', 0xb08a5a, { tex: 'crate' });
  // доска объявлений и огнетушитель — на стенах
  Df(fr, 0.012, 1.7, 0.02, 0.7, 1.0, y + 1.3, 'wood', 0x9a7a52, { tex: 'wood' });
  Df(fr, W - 0.04, 5.0, 0.07, 0.38, 0.14, y + 1.0, 'plaster', 0xb0302a, { tex: 'paintw' });
  skirtV(fr, 0.0125, 0.0, Dp, y); skirtV(fr, W - 0.0125, 0.0, Dp, y);
  World.lights.push({ x: fr.vx + fr.away * W / 2, y: r.y + DLH - 0.6, z: fr.zd + fr.dz * Dp / 2, col: 0xffe0b0, int: 0.5, dist: 10 });
  lampAt(fr.vx + fr.away * W / 2, y + DLH - SLAB - 0.06 - (r.f === 0 ? 0.03 : 0), fr.zd + fr.dz * Dp / 2, true);
}

/* ---------- санузлы и кухня (блоки у лестничных ядер) ---------- */
// окна «дальней» (наружной продольной) стены блока в координатах u: [от, до, низ, верх]
const BWIN = { wc: [[2.4, 3.0, 1.65, 2.35], [3.6, 4.2, 1.65, 2.35], [4.8, 5.4, 1.65, 2.35]], shower: [[3.45, 4.35, 1.5, 2.3]], kitchen: [[3.9, 5.1, 1.1, 2.1]] };
function wcRoom(vx, away, zd, zf, y, kind, L, f) {
  const fr = frm(vx, away, zd, zf), Dp = Math.abs(zf - zd), r = mkRoom(fr, L, Dp, y, f), tl = 0xcfd2cc;
  World.lights.push({ x: vx + away * 3, y: y + DLH - 0.5, z: (zd + zf) / 2, col: kind === 'kitchen' ? 0xffe2b0 : 0xe0ecff, int: 0.5, dist: 9 });
  lampAt(vx + away * 3, y + DLH - SLAB - 0.06 - (f === 0 ? 0.03 : 0), (zd + zf) / 2, false);
  r.keep.push({ u: 0.85, v: Dp / 2, wu: 1.7, dv: Dp }); // полоса от двери вдоль всей глубины
  const TW = (u, v, w, d, h) => Bf(fr, u, v, w, h || 1.85, d, y, 'plaster', tl, { tex: 'tile' });
  skirtV(fr, 0.0125, 0.0, Dp, y); skirtV(fr, L - 0.0125, 0.0, Dp, y); skirtU(fr, Dp - 0.0125, 0.0, L, y); skirtU(fr, 0.0125, 1.7, L, y);
  if (kind === 'wc') {
    // три кабинки у дальней стены: перегородки между ними, унитаз у стены
    for (let k = 0; k <= 3; k++) TW(2.1 + k * 1.2, Dp - 0.78, 0.05, 1.56);
    for (let k = 0; k < 3; k++) { const uc = 2.7 + k * 1.2; rmPut(r, uc, Dp - 0.33, 0.42, 0.78, 0.6, 'concrete', 0xdad8d0, { shape: 'toilet', far: fr.dz }); r.occ.push({ u: uc, v: Dp - 0.78, wu: 1.1, dv: 1.56 }); }
    for (let k = 0; k < 2; k++) { const u = 2.6 + k * 0.9; rmPut(r, u, 0.28, 0.55, 0.95, 0.4, 'concrete', 0xdad8d0, { shape: 'sink' }); Df(fr, u, 0.02, 0.5, 0.7, 0.02, y + 1.2, 'metal', 0xaab4b8); }
    rmPut(r, L - 0.4, 0.35, 0.4, 0.5, 0.4, 'metal', 0x4a5a48, { shape: 'junk' });
  } else if (kind === 'shower') {
    for (let k = 0; k <= 3; k++) TW(2.1 + k * 1.2, Dp - 0.78, 0.05, 1.56);
    for (let k = 0; k < 3; k++) { const uc = 2.7 + k * 1.2; Df(fr, uc, Dp - 0.1, 0.1, 0.1, 0.1, y + 2.1, 'metal', 0x8a8e90); Df(fr, uc, Dp - 0.04, 0.04, 2.1, 0.04, y, 'metal', 0x7d8184); r.occ.push({ u: uc, v: Dp - 0.78, wu: 1.1, dv: 1.56 }); }
    rmPut(r, 3.6, 0.28, 1.5, 0.42, 0.34, 'wood', 0x6a5a40, { shape: 'bench' });
    rmPut(r, L - 0.35, 0.6, 0.35, 0.5, 0.5, 'metal', 0x4a5a48, { shape: 'junk' });
    for (let k = 0; k < 4; k++) Df(fr, 2.3 + k * 0.45, 0.02, 0.05, 0.05, 0.04, y + 1.6, 'metal', 0x8a8e90);
  } else if (kind === 'kitchen') {
    for (let k = 0; k < 3; k++) rmPut(r, 2.3 + k * 0.72, Dp - 0.33, 0.62, 0.88, 0.62, 'metal', 0xcfcdc4, { shape: 'stove' });
    rmPut(r, 4.5, Dp - 0.33, 0.6, 0.95, 0.6, 'concrete', 0xdad8d0, { shape: 'sink' });
    rmPut(r, 5.25, Dp - 0.34, 0.62, 1.7, 0.62, 'metal', 0xd8d6cf, { shape: 'fridge', face: fcV(r, -1) });
    rmPut(r, 3.6, Dp * 0.5 - 0.1, 1.8, 0.76, 0.9, 'wood', 0x7a5c3a, { shape: 'table' });
    for (const [su, sv] of [[2.9, -0.78], [4.3, -0.78], [2.9, 0.78], [4.3, 0.78]]) rmPut(r, su, Dp * 0.5 - 0.1 + sv, 0.38, 0.42, 0.38, 'wood', 0x5a4630, { shape: 'stool' });
    Df(fr, 3.4, Dp - 0.1, 1.4, 0.5, 0.2, y + 1.55, 'wood', 0x8a7050, { tex: 'wood' }); // навесной шкаф
  }
  return r;
}

/* ---------- лестничное ядро ---------- */
function stairCore(vx, away, zc, F) {
  const VEST = 1.6, FL = 2.75, TR = FL / STEPN, LAND0 = VEST + FL, LAND1 = 5.85;
  const sx = s => vx + away * s;
  const lanes = { S: [zc + 0.15, zc + 2.25], N: [zc - 2.25, zc - 0.15] };
  const bx = (s0, s1, z0, z1, y0, y1, mat, col, opt) => B((sx(s0) + sx(s1)) / 2, y0, (z0 + z1) / 2, Math.abs(sx(s1) - sx(s0)), y1 - y0, z1 - z0, mat, col, opt);
  const flight = (lane, yStart, goesAway, solid) => {
    for (let k = 1; k <= STEPN; k++) {
      const s0 = goesAway ? VEST + (k - 1) * TR : LAND0 - k * TR, s1 = s0 + TR, top = yStart + k * RISE;
      bx(s0, s1, lanes[lane][0], lanes[lane][1], solid ? -0.1 : top - SLAB, top, 'concrete', 0xb9b5ab, { tex: 'stairs' });
    }
  };
  for (let f = 0; f < F - 1; f++) {
    const yv = f * DLH + (f === 0 ? 0.03 : 0), yl = f * DLH + 1.6;
    flight('S', yv, true, f === 0);
    bx(LAND0, LAND1, lanes.N[0], lanes.S[1], f === 0 ? -0.1 : yl - SLAB, yl, 'concrete', 0xb0ada3, { tex: 'stairs' });
    flight('N', yl, false, f === 0);
    const yb = (f + 1) * DLH;
    bx(0.1, VEST, lanes.N[0], lanes.S[1], yb - SLAB, yb, 'concrete', 0xa8a59b, { tex: 'concrete' });
  }
  // перегородка между маршами и ограждение сверху
  const yt = (F - 1) * DLH + 1.1;
  bx(VEST, LAND0, zc - 0.15, zc + 0.15, -0.1, yt, 'concrete', 0xb4b0a6, { tex: 'paintw' });
  const ft = (F - 1) * DLH;
  bx(VEST, VEST + 0.1, lanes.S[0], lanes.S[1], ft, ft + 1.1, 'metal', 0x6a5a45);
  World.lights.push({ x: sx(2.2), y: (F - 1) * DLH * 0.5 + 2.6, z: zc, col: 0xdfe6ff, int: 0.45, dist: 11 });
  return { VEST };
}

/* ---------- лестница-«пожарка» снаружи ---------- */
function escapeLayout(xs, dirx, F) {
  const TR = 0.28, N = 20, LL = 2.2, out = [];
  let x = xs;
  for (let f = 0; f < F - 1; f++) { x += dirx * N * TR; out.push({ lvl: f + 1, cx: x + dirx * LL / 2 }); x += dirx * LL; }
  return out;
}
function fireEscape(xs, dirx, zFace, dzo, F) {
  const TR = 0.28, N = 20, LL = 2.2, Wd = 1.8, z0 = zFace + dzo * 0.03, z1 = zFace + dzo * (0.03 + Wd), cz = (z0 + z1) / 2, rz = zFace + dzo * (Wd + 0.0);
  let x = xs;
  const col = 0x9a7a58;
  for (let f = 0; f < F - 1; f++) {
    const y0 = f * DLH + (f === 0 ? 0.03 : 0);
    for (let k = 1; k <= N; k++) {
      const xa = x + dirx * (k - 1) * TR, xb = xa + dirx * TR, top = y0 + k * RISE;
      B((xa + xb) / 2, f === 0 ? -0.1 : top - 0.1, cz, TR, f === 0 ? top + 0.1 : 0.1, Wd, 'metal', col, { nonav: false });
      if (k % 2 === 0) B((xa + xb) / 2, top, rz, TR * 2, 1.05, 0.05, 'metal', 0x6a5a4a);
    }
    x += dirx * N * TR;
    const yl = (f + 1) * DLH;
    B(x + dirx * LL / 2, yl - 0.1, cz, LL, 0.1, Wd, 'metal', col);
    B(x + dirx * LL / 2, yl, rz, LL, 1.05, 0.05, 'metal', 0x6a5a4a);
    B(x + dirx * LL, yl, cz, 0.05, 1.05, Wd, 'metal', 0x6a5a4a);
    x += dirx * LL;
  }
}


/* ---------- здание ---------- */
function dorm(o) {
  const F = o.F, t = 0.3, cw = 2.4, SW = o.SW, n = o.n;
  const x0 = o.x0, x1 = o.x1, z0 = o.z0, z1 = o.z1, zc = o.zc, cx = (x0 + x1) / 2, cz = (z0 + z1) / 2;
  const xb1 = x0 + SW, xb2 = x1 - SW, slot = (xb2 - xb1) / n;
  const zA = zc - cw / 2 - 0.1, zB = zc + cw / 2 + 0.1, HH = DLH - SLAB, ex = o.ext;
  const sc = k => xb1 + (k + 0.5) * slot;
  const ex_side = o.escape ? o.escape.side : 'S';
  const esc = o.escape ? escapeLayout(o.escape.xs, o.escape.dir, F) : [];
  const escAt = (lvl) => esc.find(e => e.lvl === lvl);
  const BLK = [{ vx: xb1, away: -1, xe: x0 + t / 2, kindN: 'wc', kindS: 'shower' }, { vx: xb2, away: 1, xe: x1 - t / 2, kindN: 'kitchen', kindS: 'wc' }];
  const blkWins = (blk, side) => BWIN[side === 'N' ? blk.kindN : blk.kindS].map(([ua, ub, y0, y1]) => { const xa = blk.vx + blk.away * ua, xb = blk.vx + blk.away * ub; return opw(Math.min(xa, xb), Math.max(xa, xb), y0, y1); });
  const WIN = (c) => opw(c - 0.8, c + 0.8, 0.95, 2.15); // оконный проём комнаты: 1.6 × 1.2 м, подоконник 0.95
  // ---- наружные стены ----
  for (let f = 0; f < F; f++) {
    const y = f * DLH;
    const extWall = (ax, c, a0, a1, ops) => {
      const mid = ax === 'x' ? cz : cx, sg = c < mid ? 1 : -1, ct = c - sg * 0.015, ci_ = c + sg * (t / 2 - 0.015);
      if (f === 0) {
        wallY(ax, ct, a0, a1, t - 0.03 + 0.05, y, DLH, 'concrete', 0xffffff, ops, 'concrete', 0, 0.9);
        wallY(ax, ct, a0, a1, t - 0.03, y, DLH, ex.mat, ex.col, ops, ex.tex, 0.9, DLH);
      } else wallY(ax, ct, a0, a1, t - 0.03, y, DLH, ex.mat, ex.col, ops, ex.tex);
      const lo = ax === 'x' ? a0 + t : a0, hi = ax === 'x' ? a1 - t : a1;
      wallY(ax, ci_, lo, hi, 0.03, y, HH, 'plaster', 0xffffff, ops, 'paintw', 0, HH);
      return sg;
    };
    for (const side of ['N', 'S']) {
      const ops = [], wins = [], zz = side === 'N' ? z0 : z1;
      for (let k = 0; k < n; k++) {
        const hall = f === 0 && ((side === 'S' && k === o.hallS) || (side === 'N' && k === o.hallN));
        if (hall) { ops.push(opn(sc(k), 'wide')); continue; }
        const e = side === ex_side ? escAt(f) : null;
        if (e && Math.abs(e.cx - sc(k)) < slot / 2) ops.push(opn(e.cx, 'door'));
        else { const w = WIN(sc(k)); ops.push(w); wins.push(w); }
      }
      for (const blk of BLK) for (const w of blkWins(blk, side)) { ops.push(w); wins.push(w); }
      const sg = extWall('x', zz, x0 - t / 2, x1 + t / 2, ops);
      for (const w of wins) winFrame('x', zz, w, y, sg);
    }
    for (const xx of [x0, x1]) {
      const ops = [], wins = [];
      if (f < F - 1) wins.push(opw(zc - 0.7, zc + 0.7, 2.55, 3.05));
      wins.push(opw(zc - 5.4, zc - 4.2, 1.2, 2.2), opw(zc + 4.2, zc + 5.4, 1.2, 2.2));
      for (const w of wins) ops.push(w);
      const sg = extWall('z', xx, z0 + t / 2, z1 - t / 2, ops);
      for (const w of wins) winFrame('z', xx, w, y, sg);
    }
  }
  // ---- этажи ----
  for (let f = 0; f < F; f++) {
    const y = f * DLH, yy = y + (f === 0 ? 0.03 : 0);
    // перекрытия
    slabAt(f, xb1, xb2, zA - 0.1, zB + 0.1, 'terrazzo');
    for (let k = 0; k < n; k++) {
      const a = xb1 + k * slot, b = a + slot;
      const hallN = f === 0 && k === o.hallN, hallS = f === 0 && k === o.hallS;
      slabAt(f, a, b, z0 + t / 2, zA - 0.1, hallN ? 'tile' : 'lino');
      slabAt(f, a, b, zB + 0.1, z1 - t / 2, hallS ? 'tile' : 'lino');
    }
    for (const blk of [{ xa: x0 + t / 2, xb: xb1 }, { xa: xb2, xb: x1 - t / 2 }]) {
      slabAt(f, blk.xa, blk.xb, z0 + t / 2, zc - 2.4 - 0.1, 'tile');
      slabAt(f, blk.xa, blk.xb, zc + 2.4 + 0.1, z1 - t / 2, 'tile');
      if (f === 0) slabAt(f, blk.xa, blk.xb, zc - 2.4 - 0.1, zc + 2.4 + 0.1, 'concrete');
    }
    // коридорные стены с дверными проёмами и наличниками
    const opsA = [], opsB = [];
    for (let k = 0; k < n; k++) {
      const hallN = f === 0 && k === o.hallN, hallS = f === 0 && k === o.hallS;
      opsA.push(hallN ? opw(sc(k) - 1.6, sc(k) + 1.6, 0, 2.5) : opn(sc(k), 'door'));
      opsB.push(hallS ? opw(sc(k) - 1.6, sc(k) + 1.6, 0, 2.5) : opn(sc(k), 'door'));
      if (!hallN) doorFrame('x', zA, sc(k) - 0.75, sc(k) + 0.75, 2.2, 0.2, yy);
      if (!hallS) doorFrame('x', zB, sc(k) - 0.75, sc(k) + 0.75, 2.2, 0.2, yy);
    }
    paintWall('x', zA, xb1, xb2, 0.2, y, HH, opsA);
    paintWall('x', zB, xb1, xb2, 0.2, y, HH, opsB);
    // плинтус коридора вдоль обеих стен (кроме проёмов)
    for (const [zw, dzw] of [[zA + 0.1 + 0.016, 1], [zB - 0.1 - 0.016, -1]]) {
      const ops = zw < zc ? opsA : opsB; let cur = xb1;
      for (const p of ops.slice().sort((a, b) => a.a - b.a)) { if (p.y0 > 0.2) continue; if (p.a > cur) D((cur + p.a) / 2, yy, zw, p.a - cur, 0.1, 0.02, 'wood', 0x3d3228, { tex: 'wood' }); cur = p.b; }
      if (xb2 > cur) D((cur + xb2) / 2, yy, zw, xb2 - cur, 0.1, 0.02, 'wood', 0x3d3228, { tex: 'wood' });
    }
    // перегородки между комнатами
    for (let k = 1; k < n; k++) {
      const x = xb1 + k * slot;
      wallY('z', x, z0 + t / 2, zA - 0.1, 0.15, y, HH, 'plaster', 0xffffff, [], 'wallpaper');
      wallY('z', x, zB + 0.1, z1 - t / 2, 0.15, y, HH, 'plaster', 0xffffff, [], 'wallpaper');
    }
    // торцы коридора
    paintWall('z', xb1, z0 + t / 2, z1 - t / 2, 0.2, y, HH, [opw(zc - 1.3, zc + 1.3, 0, 2.5)]);
    paintWall('z', xb2, z0 + t / 2, z1 - t / 2, 0.2, y, HH, [opw(zc - 1.3, zc + 1.3, 0, 2.5)]);
    // ядра: боковые перегородки с дверями и санузлы/кухня
    for (const blk of BLK) {
      const { vx, away } = blk, dx = vx + away * 0.8, L = Math.abs(blk.xe - vx);
      for (const zz of [zc - 2.4, zc + 2.4]) { paintWall('x', zz, Math.min(vx, blk.xe), Math.max(vx, blk.xe), 0.2, y, HH, [opn(dx, 'door')]); doorFrame('x', zz, dx - 0.75, dx + 0.75, 2.2, 0.2, yy); }
      const rN = wcRoom(vx, away, zc - 2.5, z0 + t / 2, yy, blk.kindN, L, f), rS = wcRoom(vx, away, zc + 2.5, z1 - t / 2, yy, blk.kindS, L, f);
      World.rooms.push({ f, kind: blk.kindN, id: blk.kindN, b: o.numOff, door: [dx, zc - 2.4], inn: [dx, zc - 3.5], far: [vx + away * 0.85, zc - 4.6], dropped: rN.dropped });
      World.rooms.push({ f, kind: blk.kindS, id: blk.kindS, b: o.numOff, door: [dx, zc + 2.4], inn: [dx, zc + 3.5], far: [vx + away * 0.85, zc + 4.6], dropped: rS.dropped });
      sign('z', 1, dx, y + 2.45, zc - 2.4 + 0.12, blk.kindN === 'wc' ? 'WC' : 'КУХНЯ', 0.5, 0.2, 1);
      sign('z', -1, dx, y + 2.45, zc + 2.4 - 0.12, blk.kindS === 'wc' ? 'WC' : 'ДУШ', 0.5, 0.2, 1);
    }
    // таблички этажа — на стенах коридора у лестниц (раньше висели в проёме)
    sign('z', -1, xb1 + 1.1, y + 1.95, zB - 0.1 - 0.012, (f + 1) + ' ЭТАЖ', 0.8, 0.24, 2);
    sign('z', 1, xb2 - 1.1, y + 1.95, zA + 0.1 + 0.012, (f + 1) + ' ЭТАЖ', 0.8, 0.24, 2);
    sign('z', 1, xb1 + 1.1, y + 1.95, zA + 0.1 + 0.012, (f + 1) + ' ЭТАЖ', 0.8, 0.24, 2);
    sign('z', -1, xb2 - 1.1, y + 1.95, zB - 0.1 - 0.012, (f + 1) + ' ЭТАЖ', 0.8, 0.24, 2);
    // комнаты
    for (const side of ['N', 'S']) for (let k = 0; k < n; k++) {
      const hall = f === 0 && ((side === 'S' && k === o.hallS) || (side === 'N' && k === o.hallN));
      const rx0 = xb1 + k * slot + 0.075, rx1 = xb1 + (k + 1) * slot - 0.075;
      const zd = side === 'N' ? zA - 0.1 : zB + 0.1, zf = side === 'N' ? z0 + t / 2 : z1 - t / 2;
      const id = (f + 1) * 100 + o.numOff + 2 * k + (side === 'N' ? 1 : 2);
      srand(9000 + id * 7 + o.numOff);
      const e = side === ex_side ? escAt(f) : null, isExit = !!(e && Math.abs(e.cx - sc(k)) < slot / 2);
      const W = rx1 - rx0, Dp = Math.abs(zf - zd), dz = Math.sign(zf - zd);
      const r = mkRoom(frm(rx0, 1, zd, zf), W, Dp, yy, f);
      const info = { f, id, kind: hall ? 'hall' : 'room', b: o.numOff, door: [sc(k), zd - dz * 0.1], inn: [sc(k), zd + dz * 1.0], far: [sc(k), zf - dz * 1.0], cx: rx0 + W / 2, cz: (zd + zf) / 2 };
      if (hall) {
        hallRoom(r);
      } else {
        let style = srnd() < 0.18 ? 1 : srnd() < 0.12 ? 2 : srnd() < 0.1 ? 3 : 0;
        if (isExit) style = 4;
        furnishRoom(r, style, isExit ? e.cx - rx0 : undefined);
        if (isExit) info.far = [e.cx, zf - dz * 1.0];
        if (style !== 2) World.lights.push({ x: (rx0 + rx1) / 2, y: y + DLH - 0.6, z: (zd + zf) / 2, col: 0xffd9a0, int: 0.42, dist: 7.5 });
        info.style = style;
      }
      info.dropped = r.dropped; World.rooms.push(info);
      if (!hall) {
        const sg = side === 'N' ? 1 : -1;
        sign('z', sg, sc(k) + 1.2, y + 1.85, (side === 'N' ? zA + 0.1 + 0.012 : zB - 0.1 - 0.012), String(id), 0.4, 0.2, 0);
      }
    }
    // свет и лампы в коридоре
    for (let x = xb1 + 3; x < xb2 - 1; x += 7.5) { World.lights.push({ x, y: y + DLH - 0.55, z: zc, col: f % 2 ? 0xffe2b0 : 0xe8f0ff, int: 0.55, dist: 12 }); lampAt(x, yy + DLH - SLAB - 0.06 - (f === 0 ? 0.03 : 0), zc, true); }
    World.lights.push({ x: xb1, y: y + DLH - 0.6, z: zc, col: 0xffe2b0, int: 0.4, dist: 8 });
    // немного хлама у стен коридора: между дверями, глубиной не более 0.55 м, чтобы оставалось 1.3 м прохода
    srand(7000 + f * 31 + o.numOff);
    for (let k = 1; k < n; k++) {
      if (srnd() > 0.4) continue;
      const xk = xb1 + k * slot, northSide = srnd() < 0.5, zw = northSide ? zA + 0.1 : zB - 0.1, dzw = northSide ? 1 : -1;
      if (f === 0 && (k === o.hallN || k === o.hallN + 1 || k === o.hallS || k === o.hallS + 1)) continue;
      const pick = srnd();
      if (pick < 0.35) B(xk, yy, zw + dzw * 0.28, 1.2, 0.42, 0.45, 'wood', 0x6a5236, { shape: 'bench' });
      else if (pick < 0.7) { B(xk - 0.3, yy, zw + dzw * 0.35, 0.6, 0.8, 0.6, 'wood', 0xb08a5a, { tex: 'crate' }); if (srnd() < 0.5) B(xk + 0.4, yy, zw + dzw * 0.3, 0.5, 0.5, 0.5, 'wood', 0xa0805a, { tex: 'crate' }); }
      else B(xk, yy, zw + dzw * 0.22, 1.1, 1.85, 0.4, 'metal', 0x56604f, { shape: 'locker', face: dzw > 0 ? '+z' : '-z' });
    }
    // огнетушители у лестниц
    for (const [xe, ze, dzf] of [[xb1 + 1.9, zA + 0.1 + 0.07, 1], [xb2 - 1.9, zB - 0.1 - 0.07, -1]]) D(xe, yy + 1.0, ze, 0.14, 0.4, 0.12, 'plaster', 0xb0302a, { tex: 'paintw' });
  }
  const leftV = xb1, rightV = xb2;
  stairCore(leftV, -1, zc, F);
  stairCore(rightV, 1, zc, F);
  // ---- крыша ----
  const top = F * DLH;
  B(cx, top - SLAB, cz, x1 - x0 + 0.7, SLAB + 0.12, z1 - z0 + 0.7, 'roof', 0x5f5e5a, { tex: 'roof' });
  for (const [px, pz, pw, pd] of [[cx, z0 - 0.3, x1 - x0 + 0.7, 0.2], [cx, z1 + 0.3, x1 - x0 + 0.7, 0.2], [x0 - 0.3, cz, 0.2, z1 - z0], [x1 + 0.3, cz, 0.2, z1 - z0]]) B(px, top + 0.12, pz, pw, 0.55, pd, 'concrete', 0x8c8981);
  B(cx - 6, top + 0.12, cz + 2, 1.2, 1.4, 1.2, 'brick', 0x8a5a48); B(cx + 9, top + 0.12, cz - 2, 1.2, 1.2, 1.2, 'brick', 0x8a5a48);
  const bd = { x0, x1, z0, z1, cx, cz, h: top, levels: F, wpPer: 3 };
  World.buildings.push(bd);
  // навес и ступени у входов
  for (const [side, k] of [['S', o.hallS], ['N', o.hallN]]) {
    if (k < 0) continue;
    const dz = side === 'S' ? 1 : -1, zz = side === 'S' ? z1 : z0, xc = sc(k);
    B(xc, 2.75, zz + dz * 1.3, 4.6, 0.14, 2.6, 'concrete', 0x77746c, { tex: 'concrete' });
    B(xc - 2.1, 0, zz + dz * 2.4, 0.2, 2.75, 0.2, 'metal', 0x4a4d50); B(xc + 2.1, 0, zz + dz * 2.4, 0.2, 2.75, 0.2, 'metal', 0x4a4d50);
    B(xc, 0, zz + dz * 0.95, 4.2, 0.16, 1.1, 'concrete', 0x8c8981, { tex: 'concrete' });
    B(xc, 0, zz + dz * 1.8, 4.2, 0.08, 0.7, 'concrete', 0x8c8981, { tex: 'concrete' });
  }
  if (o.escape) fireEscape(o.escape.xs, o.escape.dir, o.escape.zFace, o.escape.dz, F);
  // водосточные трубы
  for (const [px, pz] of [[x0 - 0.2, z0 - 0.2], [x1 + 0.2, z0 - 0.2], [x0 - 0.2, z1 + 0.2], [x1 + 0.2, z1 + 0.2]]) B(px, 0, pz, 0.14, top, 0.14, 'metal', 0x5a4a3a);
  return bd;
}

/* ---------- карта ---------- */
MAPS.dorms = {
  name: 'Общага', spawnMin: 40, bound: 96, spawn: [70, 44, 1.04], T: 98, pick: [14, 12], maxWP: 60, env: 'overcast',
  koth: [[-6, -4], [28, 0], [-52, -4], [30, 34]],
  gen() {
    srand(20261016);
    this.flat.push([-72, 72, -46, 54]);
    // дороги (гравий)
    this.roads.push({ x0: -98, x1: 98, z0: 40, z1: 47, tex: 'gravel' }, { x0: 56, x1: 63, z0: -98, z1: 40, tex: 'gravel' }, { x0: -62, x1: -30, z0: 26, z1: 40, tex: 'gravel' });
    // ---- Общежитие №3 (3 этажа) ----
    dorm({
      x0: -40, x1: 16, z0: -34, z1: -18, zc: -26, F: 3, SW: 6, n: 8, hallS: 3, hallN: 5, numOff: 0,
      ext: { mat: 'plaster', tex: 'plasterY', col: 0xffffff },
      escape: { xs: -2, dir: -1, zFace: -18 + 0.15, dz: 1, side: 'S' },
    });
    // ---- Общежитие №2 (2 этажа) ----
    dorm({
      x0: -30, x1: 10, z0: 8, z1: 22, zc: 15, F: 2, SW: 6, n: 5, hallS: 2, hallN: 1, numOff: 20,
      ext: { mat: 'brick', tex: 'brick', col: 0xcaa896 },
      escape: { xs: 4, dir: -1, zFace: 8 - 0.15, dz: -1, side: 'N' },
    });
    outdoor.call(this);
  },
};

function outdoor() {
  const W = this;
  const occ = [];
  const inB = (x, z, m) => W.buildings.some(b => x > b.x0 - m && x < b.x1 + m && z > b.z0 - m && z < b.z1 + m);
  const onRoad = (x, z, m) => W.roads.some(r => x > r.x0 - m && x < r.x1 + m && z > r.z0 - m && z < r.z1 + m);
  const spot = (r, area) => {
    for (let k = 0; k < 60; k++) {
      const x = srr(area[0], area[1]), z = srr(area[2], area[3]);
      if (inB(x, z, r + 3) || onRoad(x, z, r + 0.5) || Math.hypot(x - W.spawnPlayer[0], z - W.spawnPlayer[1]) < 8) continue;
      if (occ.every(o => Math.hypot(o[0] - x, o[1] - z) > o[2] + r)) { occ.push([x, z, r]); return [x, z]; }
    }
    return null;
  };
  const yard = [-60, 60, -16, 36];
  // детская площадка
  const px = 32, pz = -2;
  occ.push([px, pz, 9]);
  B(px, 0, pz + 3, 4.2, 0.35, 4.2, 'wood', 0x6a5a40, { tex: 'wood' }); // песочница
  B(px - 3, 0, pz - 3, 0.12, 2.4, 0.12, 'metal', 0x6a3a2a); B(px - 0.5, 0, pz - 3, 0.12, 2.4, 0.12, 'metal', 0x6a3a2a);
  B(px - 1.75, 2.3, pz - 3, 2.8, 0.1, 0.1, 'metal', 0x6a3a2a); // качели
  B(px - 1.2, 0.5, pz - 3, 0.5, 0.06, 0.3, 'wood', 0x7a5a3a, { vis: true });
  B(px + 4, 0, pz - 2, 0.9, 1.5, 2.6, 'metal', 0x7a3b30, { shape: 'junk' }); // горка
  B(px + 4, 0, pz + 1, 0.5, 0.7, 0.5, 'metal', 0x4a6a4a);
  B(px - 6, 0, pz + 2, 1.8, 0.5, 0.4, 'wood', 0x6a5a40, { tex: 'wood' }); // лавка
  B(px + 7, 0, pz + 4, 1.8, 0.5, 0.4, 'wood', 0x6a5a40, { tex: 'wood' });
  // машины-развалюхи
  const rust = [0x7a4a30, 0x6a4a3a, 0x56595a, 0x4f6a50, 0x8a7a5a];
  const carsAt = [[-18, 31, false], [-8, 31.5, false], [24, 30, false], [44, 28, true], [-52, 18, true], [66, 20, true], [-62, -8, true], [20, -50, false]];
  carsAt.forEach((c, i) => { if (!inB(c[0], c[1], 3)) { car(c[0], c[1], c[2], rust[i % rust.length]); occ.push([c[0], c[1], 3]); } });
  // мусор и контейнеры
  const dump = (x, z, r) => {
    if (inB(x, z, 3)) return;
    B(x, 0, z, 2.0, 1.2, 1.1, 'metal', 0x3f5a46, { tex: 'container' }); occ.push([x, z, 2]);
    for (let i = 0; i < 6; i++) { const s = srr(0.4, 0.9); B(x + srr(-r, r), 0, z + srr(-r, r) + 1.6, s * 1.3, srr(0.2, 0.5), s, 'wood', [0x5a4a3a, 0x3a3a38, 0x6b5f4a][i % 3], { shape: 'junk' }); }
  };
  dump(-46, -14, 1.4); dump(24, -14, 1.2); dump(-40, 4, 1.2); dump(14, 28, 1.2);
  // бочки, ящики, покрышки, стройматериалы
  for (let i = 0; i < 22; i++) { const p = spot(1, yard); if (p) { const s = srnd(); if (s < 0.4) { B(p[0], 0, p[1], 0.62, 0.95, 0.62, 'metal', 0x44603f, { shape: 'cyl' }); } else if (s < 0.75) crate(p[0], p[1], 0, 1.1); else B(p[0], 0, p[1], 1.3, 0.6, 1.3, 'concrete', 0x3a3a3a, { shape: 'rock' }); } }
  for (let i = 0; i < 8; i++) { const p = spot(2, [-70, 70, -44, 52]); if (p) barrier(p[0], p[1], srnd() < 0.5); }
  // поленницы и штабеля
  for (const [x, z] of [[-36, -40], [-46, 12]]) if (!inB(x, z, 3)) { B(x, 0, z, 3, 1.1, 1.0, 'wood', 0x7a5a3a, { tex: 'wood' }); occ.push([x, z, 2]); }
  // забор по периметру двора (бетонные плиты и сетка)
  const fenceCol = 0x9a978d;
  for (let x = -60; x < 62; x += 3.1) { if (x > 4 && x < 14) continue; B(x + 1.5, 0, -46, 3, 2.4, 0.18, 'concrete', fenceCol, { tex: 'concrete' }); }
  for (let z = -46; z < 36; z += 3.1) { if (z > -12 && z < -4) continue; B(-62, 0, z + 1.5, 0.18, 2.4, 3, 'concrete', fenceCol, { tex: 'concrete' }); }
  for (let z = -46; z < 36; z += 3.1) { if (z > 6 && z < 14) continue; B(62, 0, z + 1.5, 0.18, 2.4, 3, 'concrete', fenceCol, { tex: 'concrete' }); }
  // деревья: двор и лес
  const T = (x, z, s, low) => tree(x, z, s, low);
  for (let i = 0; i < 26; i++) { const p = spot(1.2, [-58, 58, -42, 38]); if (p) T(p[0], p[1], srr(0.9, 1.5)); }
  for (let i = 0; i < 520; i++) {
    const x = srr(-95, 95), z = srr(-95, 95);
    if (x > -66 && x < 66 && z > -50 && z < 56) continue;
    if (onRoad(x, z, 3.5)) continue;
    if (Math.hypot(x - W.spawnPlayer[0], z - W.spawnPlayer[1]) < 8) continue;
    T(x, z, srr(1.0, 1.8), Math.max(Math.abs(x) - 66, z - 56, -50 - z) > 18);
  }
  // граница карты (невидимая стена)
  const E = W.T;
  B(0, 0, -E, 2 * E + 4, 6, 1, 'concrete', 0x8c897f, { vis: false }); B(0, 0, E, 2 * E + 4, 6, 1, 'concrete', 0x8c897f, { vis: false });
  B(-E, 0, 0, 1, 6, 2 * E + 4, 'concrete', 0x8c897f, { vis: false }); B(E, 0, 0, 1, 6, 2 * E + 4, 'concrete', 0x8c897f, { vis: false });
  // подсказки для путевых точек: коридоры и дворы
  for (let f = 0; f < 3; f++) for (let x = -34; x <= 10; x += 11) W.hintWP.push([x, -26, f * DLH]);
  for (let f = 0; f < 2; f++) for (let x = -24; x <= 4; x += 9) W.hintWP.push([x, 15, f * DLH]);
  W.hintWP.push([-6, -4, 0], [28, 0, 0], [-52, -4, 0], [30, 34, 0], [-20, 6, 0], [20, 14, 0]);
}

/* --- 20_ballistics.js --- */
/* ===== Патроны, оружие, внешняя баллистика ===== */
const RHO = 1.225;
const CART = {
  c556: { name: '5.56x45 M855', dmg: 54, pen: 31, v: 922, mass: 0.0040, cal: 0.00556, cd: 0.30 },
  c762: { name: '7.62x39 PS',   dmg: 57, pen: 35, v: 715, mass: 0.0079, cal: 0.00762, cd: 0.33 },
  c9:   { name: '9x19 Pst',     dmg: 52, pen: 20, v: 360, mass: 0.0075, cal: 0.00900, cd: 0.36 },
};
for (const k in CART) { const c = CART[k]; c.k = 0.5 * RHO * c.cd * Math.PI * (c.cal / 2) ** 2 / c.mass; }

// коэффициент сопротивления в зависимости от числа Маха (трансзвуковой скачок)
function dragMul(m) {
  if (m < 0.8) return 0.82;
  if (m < 1.0) return 0.82 + (m - 0.8) / 0.2 * 0.6;
  if (m < 1.25) return 1.42 - (m - 1.0) / 0.25 * 0.3;
  return Math.max(0.78, 1.12 - (m - 1.25) * 0.18);
}

const WEAPONS = {
  m4: {
    id: 'm4', name: 'M4A1', cart: 'c556', rpm: 800, mag: 30, modes: ['auto', 'semi'], kind: 'rifle',
    recV: 0.0078, recH: 0.0030, moa: 2.2, reload: { tac: 2.35, empty: 3.1 }, adsTime: 0.2,
    zeroSteps: [50, 100, 150, 200, 300, 400], zero0: 1, loud: 1,
    eyeRel: 0.2, zeroBias: 0.0012, sightH: 0.071, muzzleZ: 0.483, gripR: [0, -0.176, 0.062], gripL: [0, -0.07, -0.24], magPos: [0, -0.145, -0.085], rackPos: [0, -0.025, 0.09],
  },
  akm: {
    id: 'akm', name: 'AKM', cart: 'c762', rpm: 600, mag: 30, modes: ['auto', 'semi'], kind: 'rifle',
    recV: 0.0125, recH: 0.0052, moa: 3.4, reload: { tac: 2.6, empty: 3.5 }, adsTime: 0.24,
    zeroSteps: [50, 100, 150, 200, 300, 400], zero0: 1, loud: 1.15,
    eyeRel: 0.25, sightH: 0.052, muzzleZ: 0.405, gripR: [0, -0.15, 0.212], gripL: [0, -0.07, -0.11], magPos: [0, -0.082, 0.048], rackPos: [0, -0.043, 0.125],
  },
  glock: {
    id: 'glock', name: 'G17', cart: 'c9', rpm: 450, mag: 17, modes: ['semi'], kind: 'pistol',
    recV: 0.020, recH: 0.0060, moa: 5.5, reload: { tac: 1.7, empty: 2.2 }, adsTime: 0.14,
    zeroSteps: [25, 50, 75], zero0: 1, loud: 0.7,
    eyeRel: 0.30, sightH: 0.027, muzzleZ: 0.178, gripR: [0, -0.092, 0.030], gripL: [0.018, -0.088, 0.034], magPos: [0, -0.150, 0.040], rackPos: [0, -0.022, 0.004],
  },
};

/* ---------- пересечение луча с капсулой ---------- */
function rayCapsule(ox, oy, oz, dx, dy, dz, len, a, b, r) {
  const bax = b[0] - a[0], bay = b[1] - a[1], baz = b[2] - a[2];
  const oax = ox - a[0], oay = oy - a[1], oaz = oz - a[2];
  const baba = bax * bax + bay * bay + baz * baz;
  const rr = r * r;
  if (baba < 1e-6) {
    const bq = dx * oax + dy * oay + dz * oaz, cq = oax * oax + oay * oay + oaz * oaz - rr, hq = bq * bq - cq;
    if (hq < 0) return -1;
    const t = -bq - Math.sqrt(hq);
    return t >= 0 && t <= len ? t : -1;
  }
  const bard = bax * dx + bay * dy + baz * dz;
  const baoa = bax * oax + bay * oay + baz * oaz;
  const rdoa = dx * oax + dy * oay + dz * oaz;
  const oaoa = oax * oax + oay * oay + oaz * oaz;
  const A = baba - bard * bard, Bq = baba * rdoa - baoa * bard, C = baba * oaoa - baoa * baoa - rr * baba;
  const h = Bq * Bq - A * C;
  if (h < 0) return -1;
  if (A > 1e-9) {
    const t = (-Bq - Math.sqrt(h)) / A;
    const y = baoa + t * bard;
    if (y > 0 && y < baba) return t >= 0 && t <= len ? t : -1;
  }
  const y2 = baoa + ((-Bq - Math.sqrt(h)) / (A > 1e-9 ? A : 1)) * bard;
  const ex = y2 <= 0 ? oax : ox - b[0], ey = y2 <= 0 ? oay : oy - b[1], ez = y2 <= 0 ? oaz : oz - b[2];
  const b2 = dx * ex + dy * ey + dz * ez, c2 = ex * ex + ey * ey + ez * ez - rr, h2 = b2 * b2 - c2;
  if (h2 > 0) { const t = -b2 - Math.sqrt(h2); return t >= 0 && t <= len ? t : -1; }
  return -1;
}

/* ---------- пули ---------- */
const Ballistics = {
  list: [], acc: 0, STEP: 1 / 120,
  spawn(owner, cart, o, d, tracer, opt) {
    const sp = cart.v * (1 + rnd(-0.012, 0.012));
    this.list.push({
      x: o[0], y: o[1], z: o[2], vx: d[0] * sp, vy: d[1] * sp, vz: d[2] * sp,
      cart, owner, pen: cart.pen, pen0: cart.pen, dmgScale: 1, age: 0, dist: 0, tracer: !!tracer, rico: 0, whiz: false,
      sx: o[0], sy: o[1], sz: o[2], cos: !!(opt && opt.cos), lag: (opt && opt.lag) || 0,
    });
  },
  update(dt) {
    this.acc += dt;
    let n = 0;
    while (this.acc >= this.STEP && n++ < 8) { this.acc -= this.STEP; this.step(this.STEP); }
    if (this.acc > this.STEP * 8) this.acc = 0;
  },
  step(dt) {
    for (let i = this.list.length - 1; i >= 0; i--) {
      const b = this.list[i];
      const v = Math.hypot(b.vx, b.vy, b.vz);
      const k = b.cart.k * dragMul(v / SOUND) * v;
      const nvx = b.vx - b.vx * k * dt, nvy = b.vy - b.vy * k * dt - G * dt, nvz = b.vz - b.vz * k * dt;
      const mx = (b.vx + nvx) / 2 * dt, my = (b.vy + nvy) / 2 * dt, mz = (b.vz + nvz) / 2 * dt;
      const len = Math.hypot(mx, my, mz);
      b.vx = nvx; b.vy = nvy; b.vz = nvz; b.age += dt;
      const sp = Math.hypot(nvx, nvy, nvz);
      if (len < 1e-6 || sp < 45 || b.age > 8 || b.y < -6 || Math.abs(b.x) > 220 || Math.abs(b.z) > 220) { this.list.splice(i, 1); continue; }
      this.nearMiss(b, mx / len, my / len, mz / len, len, sp);
      const cont = this.advance(b, mx / len, my / len, mz / len, len);
      b.dist += len;
      if (!cont) this.list.splice(i, 1);
    }
  },
  nearMiss(b, dx, dy, dz, len, sp) {
    if (sp < 250) return;
    for (const c of Game.combatants) {
      if (!c.alive || c === b.owner) continue;
      if (b.cos && !c.isPlayer) continue;
      const cx = c.x - b.x, cy = c.y + 1.3 - b.y, cz = c.z - b.z;
      const t = clamp(cx * dx + cy * dy + cz * dz, 0, len);
      const px = cx - dx * t, py = cy - dy * t, pz = cz - dz * t;
      const d = Math.hypot(px, py, pz);
      if (d < 2.6) {
        c.suppress = Math.min(1, c.suppress + 0.4 * (1 - d / 2.6));
        c.lastShotAt = [b.owner ? b.owner.x : b.sx, b.owner ? b.owner.z : b.sz];
        c.lastShotT = Game.time;
        if (c.isPlayer && !b.whiz && d < 5) { b.whiz = true; Bus.emit('whiz', { dist: d, supersonic: sp > SOUND, x: b.x + dx * t, y: b.y + dy * t, z: b.z + dz * t }); }
      }
    }
  },
  advance(b, dx, dy, dz, len) {
    let ox = b.x, oy = b.y, oz = b.z;
    for (let guard = 0; guard < 6 && len > 1e-4; guard++) {
      let best = null, bt = len;
      const wh = World.rayBoxes(ox, oy, oz, dx, dy, dz, len);
      if (wh) { best = { type: 'world', t: wh.t, h: wh }; bt = wh.t; }
      const tg = World.rayTerrain(ox, oy, oz, dx, dy, dz, bt);
      if (tg && tg.t < bt) { best = { type: 'ground', t: tg.t, n: tg }; bt = tg.t; }
      if (!b.cos) for (const c of Game.combatants) {
        if (!c.alive || c === b.owner || !c.rig) continue;
        if (c.protT > 0) continue;
        if (Game.noFF && b.owner && c.team === b.owner.team) continue;
        const hh = b.lag > 0 && c.hist ? c.histAt(b.lag) : null, ccx = hh ? hh.x : c.x, ccy = hh ? hh.y : c.y, ccz = hh ? hh.z : c.z, caps = hh ? hh.caps : c.rig.caps;
        const cx = ccx - ox, cy = ccy + 0.95 - oy, cz = ccz - oz;
        const proj = clamp(cx * dx + cy * dy + cz * dz, 0, len);
        const px = cx - dx * proj, py = cy - dy * proj, pz = cz - dz * proj;
        if (px * px + py * py + pz * pz > 2.4) continue;
        for (const cap of caps) {
          const t = rayCapsule(ox, oy, oz, dx, dy, dz, bt, cap.a, cap.b, cap.r);
          if (t >= 0 && t < bt) { bt = t; best = { type: 'char', t, c, part: cap.part }; }
        }
      }
      if (!best) { b.x = ox + dx * len; b.y = oy + dy * len; b.z = oz + dz * len; return true; }
      const hx = ox + dx * best.t, hy = oy + dy * best.t, hz = oz + dz * best.t;
      if (best.type === 'char') {
        Combat.hitCombatant(best.c, best.part, b, [hx, hy, hz], [dx, dy, dz]);
        return false;
      }
      let nx, ny, nz, matName, thick = 0, texit = 0;
      if (best.type === 'ground') { nx = best.n.nx; ny = best.n.ny; nz = best.n.nz; matName = 'dirt'; thick = 999; }
      else { const h = best.h; nx = h.nx; ny = h.ny; nz = h.nz; matName = h.box.mat; thick = h.tExit - h.t; texit = h.tExit; }
      const mat = MATS[matName] || MATS.concrete;
      const cosA = Math.abs(dx * nx + dy * ny + dz * nz);
      const sp = Math.hypot(b.vx, b.vy, b.vz);
      // рикошет
      if ((mat.hard || best.type === 'ground') && cosA < (best.type === 'ground' ? 0.12 : 0.26) && b.rico < 2 && Math.random() < 0.7) {
        const dn = dx * nx + dy * ny + dz * nz;
        let rx = dx - 2 * dn * nx + rnd(-0.06, 0.06), ry = dy - 2 * dn * ny + rnd(-0.06, 0.06), rz = dz - 2 * dn * nz + rnd(-0.06, 0.06);
        const rl = Math.hypot(rx, ry, rz); rx /= rl; ry /= rl; rz /= rl;
        const ns = sp * 0.55;
        b.vx = rx * ns; b.vy = ry * ns; b.vz = rz * ns;
        b.rico++; b.pen *= 0.4; b.dmgScale *= 0.45;
        Bus.emit('impact', { x: hx, y: hy, z: hz, nx, ny, nz, mat: matName, rico: true, decal: false });
        ox = hx + nx * 0.03; oy = hy + ny * 0.03; oz = hz + nz * 0.03;
        len -= best.t; dx = rx; dy = ry; dz = rz;
        if (best.type === 'ground') { const hh = World.H(ox, oz) + 0.02; if (oy < hh) oy = hh; }
        continue;
      }
      // пробитие
      const cost = thick * mat.cost;
      if (best.type === 'world' && b.pen > cost && sp > 80) {
        b.pen -= cost;
        const f = Math.sqrt(Math.max(0.2, b.pen / b.pen0));
        b.vx *= f; b.vy *= f; b.vz *= f; b.dmgScale *= (0.55 + 0.45 * f);
        Bus.emit('impact', { x: hx, y: hy, z: hz, nx, ny, nz, mat: matName, pen: true, decal: true });
        const ex = ox + dx * (texit + 0.004), ey = oy + dy * (texit + 0.004), ez = oz + dz * (texit + 0.004);
        Bus.emit('impact', { x: ex, y: ey, z: ez, nx: -nx, ny: -ny, nz: -nz, mat: matName, exit: true, decal: true });
        // небольшое отклонение траектории после пробития
        let qx = dx + rnd(-0.015, 0.015), qy = dy + rnd(-0.015, 0.015), qz = dz + rnd(-0.015, 0.015);
        const ql = Math.hypot(qx, qy, qz); dx = qx / ql; dy = qy / ql; dz = qz / ql;
        const ns = Math.hypot(b.vx, b.vy, b.vz);
        b.vx = dx * ns; b.vy = dy * ns; b.vz = dz * ns;
        len -= texit + 0.004; ox = ex; oy = ey; oz = ez;
        continue;
      }
      Bus.emit('impact', { x: hx, y: hy, z: hz, nx, ny, nz, mat: matName, decal: true });
      return false;
    }
    b.x = ox; b.y = oy; b.z = oz;
    return true;
  },
};

// упреждение и превышение для ботов и расчёт нулевой точки прицела
function avgSpeed(cart, dist) { return cart.v * Math.exp(-cart.k * 0.95 * dist * 0.5 * 1.0) * 0.99; }
const _ftC = {};
function flightTime(cart, dist) {
  // интегрируем ту же модель, что и в полёте пули (сопротивление с поправкой на Мах), чтобы пристрелка совпадала с реальной траекторией
  const key = cart.name + '|' + Math.round(dist * 2), c = _ftC[key]; if (c !== undefined) return c;
  const dt = 1 / 480; let x = 0, v = cart.v, t = 0;
  while (x < dist && t < 6 && v > 20) {
    const k = cart.k * dragMul(v / SOUND) * v;
    const nv = v - v * k * dt; x += (v + nv) / 2 * dt; v = nv; t += dt;
  }
  return (_ftC[key] = t);
}
function dropAt(cart, dist) { const t = flightTime(cart, dist); return 0.5 * G * t * t; }

if (typeof module !== 'undefined') module.exports = { CART, WEAPONS, Ballistics, rayCapsule, flightTime, dropAt, dragMul };

/* --- 29_gait.js --- */
/* Походка из клипов Mixamo Walk/Run (Soldier.glb из примеров three.js): форма траектории ноги, подъём, наклон стопы, качание таза.
   Фаза u=0 — середина маха левой ноги. */
const GAIT = {"walk":{"dur":1.033,"A":0.4567,"lift":0.1702,"hipH":0.997,"z":[-0.0,0.122,0.243,0.363,0.483,0.601,0.717,0.833,0.937,0.997,0.976,0.902,0.78,0.633,0.471,0.29,0.085,-0.145,-0.398,-0.642,-0.843,-0.968,-0.999,-0.96,-0.893,-0.814,-0.7,-0.578,-0.462,-0.349,-0.236,-0.12],"y":[0.006,0.006,0.007,0.011,0.025,0.044,0.072,0.129,0.229,0.356,0.483,0.704,0.903,0.996,0.956,0.82,0.621,0.411,0.238,0.242,0.322,0.389,0.351,0.234,0.116,0.032,0.001,0.005,0.007,0.008,0.007,0.007],"p":[-0.0,-0.0,-0.0,0.003,0.015,0.033,0.062,0.13,0.266,0.504,0.777,0.629,0.561,0.651,0.791,0.785,0.556,0.303,0.049,-0.184,-0.419,-0.615,-0.635,-0.475,-0.252,-0.061,-0.003,0.0,0.0,0.0,0.0,-0.0],"b":[0.0125,0.0219,0.0263,0.0262,0.0218,0.0138,0.0039,-0.0087,-0.0192,-0.0274,-0.033,-0.0324,-0.0261,-0.0139,0.0024,0.0201,0.0363,0.0466,0.0493,0.042,0.0273,0.0102,-0.004,-0.0143,-0.0194,-0.0242,-0.0305,-0.0347,-0.0337,-0.026,-0.0133,0.0002],"s":[-0.0261,-0.0233,-0.0207,-0.0177,-0.0142,-0.0106,-0.0064,-0.0006,0.0063,0.0133,0.0202,0.0268,0.0314,0.0322,0.0294,0.0251,0.0209,0.0194,0.0176,0.0154,0.0133,0.0108,0.0075,0.0031,-0.0032,-0.0105,-0.0173,-0.0233,-0.0281,-0.0308,-0.031,-0.029]},"run":{"dur":0.7,"A":0.4748,"lift":0.4243,"hipH":0.9537,"z":[0.0,0.214,0.427,0.608,0.749,0.839,0.905,0.962,0.993,0.971,0.896,0.814,0.728,0.633,0.512,0.381,0.254,0.138,0.02,-0.115,-0.266,-0.427,-0.587,-0.747,-0.887,-0.977,-0.964,-0.888,-0.781,-0.62,-0.425,-0.215],"y":[0.001,0.002,0.002,0.035,0.101,0.176,0.27,0.386,0.513,0.64,0.769,0.872,0.941,0.987,0.996,0.983,0.961,0.898,0.816,0.733,0.643,0.558,0.487,0.408,0.331,0.254,0.177,0.103,0.047,0.013,0.003,0.004],"p":[-0.0,0.0,0.003,0.107,0.318,0.629,0.804,0.752,0.602,0.449,0.299,0.176,0.079,0.006,0.007,0.091,0.246,0.482,0.692,0.663,0.443,0.183,-0.07,-0.275,-0.44,-0.57,-0.601,-0.507,-0.241,-0.066,-0.011,0.0],"b":[-0.0551,-0.0535,-0.0419,-0.0232,-0.0022,0.0161,0.03,0.0404,0.0457,0.0459,0.0422,0.0324,0.0169,-0.0026,-0.0215,-0.0366,-0.0474,-0.0466,-0.0369,-0.021,-0.0044,0.0111,0.0259,0.0354,0.0404,0.0416,0.0355,0.0231,0.0044,-0.0146,-0.0318,-0.0477],"s":[0.0085,0.0129,0.0136,0.0121,0.01,0.0068,0.0047,0.0043,0.0056,0.007,0.0076,0.0068,0.0043,0.0003,-0.0029,-0.0053,-0.0077,-0.0093,-0.0099,-0.0094,-0.0082,-0.007,-0.0063,-0.0059,-0.0055,-0.0054,-0.0057,-0.0062,-0.0061,-0.0048,-0.002,0.0029]}};
function gaitSamp(a, u) { const n = a.length, x = (u - Math.floor(u)) * n, i = Math.floor(x) % n, f = x - Math.floor(x); return a[i] + (a[(i + 1) % n] - a[i]) * f; }
// нога: смещение вперёд (м, в амплитуде шага), подъём (м), наклон стопы (рад, + носок вниз)
function gaitFoot(ph, speed, hurt) {
  const u = ph / (Math.PI * 2), w = sm01((speed - 3.2) / 1.8), W = GAIT.walk, Rn = GAIT.run;
  const fade = sm01((speed - 0.4) / 0.9);
  const z = lerp(gaitSamp(W.z, u), gaitSamp(Rn.z, u), w), y = lerp(gaitSamp(W.y, u), gaitSamp(Rn.y, u), w), p = lerp(gaitSamp(W.p, u), gaitSamp(Rn.p, u), w);
  const lift = lerp(W.lift, Rn.lift, w) * 0.88 * (0.7 + 0.3 * w) * (0.3 + 0.7 * fade) * (hurt ? 0.5 : 1);
  return { off: z * 0.36 * fade * (hurt ? 0.7 : 1), ly: y * lift, pitch: p * 0.8 * fade };
}
// таз: подъём и качание в сторону (м), фаза привязана к левой ноге (gait + π)
function gaitBody(gait, speed) {
  const u = (gait + Math.PI) / (Math.PI * 2), w = sm01((speed - 3.2) / 1.8), W = GAIT.walk, Rn = GAIT.run, fade = sm01((speed - 0.4) / 0.9), k = 0.88 * 0.6 * fade;
  return { bob: lerp(gaitSamp(W.b, u), gaitSamp(Rn.b, u), w) * k, sway: lerp(gaitSamp(W.s, u), gaitSamp(Rn.s, u), w) * k };
}

/* --- 30_combat.js --- */
/* ===== Бойцы: тело, урон по частям, статусы, оружие, скелет ===== */
const PARTS = ['head', 'thorax', 'stomach', 'lArm', 'rArm', 'lLeg', 'rLeg'];
const PART_MAX = { head: 35, thorax: 85, stomach: 70, lArm: 60, rArm: 60, lLeg: 65, rLeg: 65 };
const PART_MUL = { head: 1, thorax: 1, stomach: 1.5, lArm: 0.7, rArm: 0.7, lLeg: 0.7, rLeg: 0.7 };
const PART_RU = { head: 'Голова', thorax: 'Грудь', stomach: 'Живот', lArm: 'Л. рука', rArm: 'П. рука', lLeg: 'Л. нога', rLeg: 'П. нога' };
const BLUNT = [0, 0.55, 0.46, 0.38, 0.30, 0.22, 0.16];
const BLEED_L = { head: 0.2, thorax: 0.28, stomach: 0.35, lArm: 0.3, rArm: 0.3, lLeg: 0.3, rLeg: 0.3 };
const BLEED_H = { head: 0.08, thorax: 0.12, stomach: 0.16, lArm: 0.1, rArm: 0.1, lLeg: 0.1, rLeg: 0.1 };
const ITEMS = {
  bandage: { ru: 'Бинт', t: 3.0 }, tourniquet: { ru: 'Жгут', t: 3.2 }, splint: { ru: 'Шина', t: 4.5 },
  pills: { ru: 'Анальгетик', t: 2.4 }, medkit: { ru: 'Аптечка', t: 6.0 },
};
const ARMOR_SETS = {
  0: null,
  3: { head: [3, 40, 0.5], thorax: [3, 55, 0.95], stomach: [2, 40, 0.8] },
  5: { head: [4, 50, 0.55], thorax: [5, 80, 0.95], stomach: [3, 55, 0.85] },
};

/* ---------- IK из двух костей ---------- */
function ik2(S, T, l1, l2, pole) {
  let dx = T[0] - S[0], dy = T[1] - S[1], dz = T[2] - S[2];
  const d = Math.max(Math.hypot(dx, dy, dz), 0.05);
  const ux = dx / d, uy = dy / d, uz = dz / d;
  const dd = Math.min(d, l1 + l2 - 0.003);
  const a = (l1 * l1 - l2 * l2 + dd * dd) / (2 * dd);
  const h = Math.sqrt(Math.max(0, l1 * l1 - a * a));
  let px = pole[0], py = pole[1], pz = pole[2];
  const dp = px * ux + py * uy + pz * uz; px -= ux * dp; py -= uy * dp; pz -= uz * dp;
  const pl = Math.hypot(px, py, pz) || 1; px /= pl; py /= pl; pz /= pl;
  return [[S[0] + ux * a + px * h, S[1] + uy * a + py * h, S[2] + uz * a + pz * h], [S[0] + ux * dd, S[1] + uy * dd, S[2] + uz * dd]];
}
const ARM1 = 0.30, ARM2 = 0.33, LEG1 = 0.45, LEG2 = 0.45;

/* ---------- поза -> скелет ---------- */
function weaponWorld(p, l) { return [p.W0[0] + p.wr[0] * l[0] + p.wu[0] * l[1] - p.wf[0] * l[2], p.W0[1] + p.wr[1] * l[0] + p.wu[1] * l[1] - p.wf[1] * l[2], p.W0[2] + p.wr[2] * l[0] + p.wu[2] * l[1] - p.wf[2] * l[2]]; }

function standPose(c) {
  const s = Math.sin(c.yaw), co = Math.cos(c.yaw);
  const F = [-s, 0, -co], R = [co, 0, -s], U = [0, 1, 0];
  const k = c.crouch, lean = c.leanA;
  const P = [c.x, c.y + 0.90 - 0.34 * k, c.z];
  const tp = clamp(-c.pitch * 0.30, -0.30, 0.40) + 0.32 * k;
  const sd = V.norm([R[0] * lean * 0.5 + F[0] * tp, 1, R[2] * lean * 0.5 + F[2] * tp]);
  const C = V.mad(P, sd, 0.37);
  const cr = V.norm(V.mad(R, sd, -V.dot(R, sd)));
  const cf = V.cross(sd, cr);
  const hf = fwdVec(c.yaw, clamp(c.pitch * 0.8, -1.2, 1.2));
  const hu = V.cross(R, hf);
  const H = V.add(V.mad(C, sd, 0.34), V.mul(cf, 0.02));
  const low = c.lowReady;
  const wp = clamp(c.pitch + c.punchP * 0.5 - low * 0.75 + (c.reloadT >= 0 ? 0.25 : 0), -1.4, 1.4);
  const a = fwdVec(c.yaw + c.punchY * 0.5 + c.swayY, wp + c.swayP);
  const wr = V.norm(V.cross(a, U)), wu = V.cross(wr, a);
  const SR = V.add(V.mad(C, cr, 0.20), V.mul(sd, 0.15));
  const W0 = V.add(V.add(V.mad(SR, a, 0.27 - low * 0.05), V.mul(wr, -0.06)), V.mul(wu, -0.05 - low * 0.06));
  const p = {
    P, pr: R, pu: U, pf: F, C, cr, cu: sd, cf, H, hr: R, hu, hf, W0, wr, wu, wf: a,
    polR: V.norm([R[0] * 0.7 - 0, -1, R[2] * 0.7]), polL: V.norm([-R[0] * 0.8, -1, -R[2] * 0.8]),
    kp: [F[0], 0, F[2]], R, F, SRoff: 0.20,
  };
  const def = c.weapon.def;
  p.tR = weaponWorld(p, def.gripR);
  p.tL = weaponWorld(p, def.gripL);
  // анимации рук
  if (c.healing) {
    const q = Math.sin(clamp(c.healing.t / c.healing.dur, 0, 1) * Math.PI);
    p.tR = V.add(V.add(V.mad(C, cf, 0.26), V.mul(cr, 0.10)), V.mul(sd, -0.10 + q * 0.04));
    p.tL = V.add(V.add(V.mad(C, cf, 0.24 + q * 0.06), V.mul(cr, -0.10)), V.mul(sd, -0.05));
  } else if (c.reloadT >= 0) {
    const pr = c.reloadT / c.reloadDur, hg = p.tL;
    const mag = weaponWorld(p, def.magPos), rack = weaponWorld(p, def.rackPos);
    const pouch = V.add(V.add(V.mad(C, cf, 0.20), V.mul(cr, -0.14)), V.mul(sd, -0.22));
    const K = [[0, hg], [0.18, mag], [0.40, pouch], [0.50, pouch], [0.64, mag], [0.78, mag]];
    if (c.reloadKind === 'empty') K.push([0.84, rack], [0.92, rack], [1, hg]); else K.push([0.9, hg], [1, hg]);
    let out = K[K.length - 1][1];
    for (let i = 0; i < K.length - 1; i++) if (pr <= K[i + 1][0]) { out = V.lerp(K[i][1], K[i + 1][1], sm01((pr - K[i][0]) / (K[i + 1][0] - K[i][0]))); break; }
    p.tL = out;
  }
  if (c.throwT >= 0) {
    const SRp = V.add(V.mad(C, cr, 0.20), V.mul(sd, 0.15)), grip = weaponWorld(p, def.gripR);
    const wind = V.add(V.add(V.mad(SRp, cr, 0.10), V.mul(sd, 0.24)), V.mul(cf, -0.22));
    const rel = V.add(V.add(V.mad(SRp, cf, 0.55), V.mul(sd, 0.02)), V.mul(cr, 0.04));
    if (!c.throwRel) p.tR = V.lerp(grip, wind, sm01(c.throwT / 0.4));
    else { const q = c.throwT - c.throwRelT; p.tR = q < 0.12 ? V.lerp(wind, rel, sm01(q / 0.12)) : V.lerp(rel, grip, sm01((q - 0.12) / 0.32)); }
  } else if (c.meleeT >= 0) {
    const SRp = V.add(V.mad(C, cr, 0.20), V.mul(sd, 0.15)), grip = weaponWorld(p, def.gripR), q = c.meleeT;
    let a, b;
    if (c.meleeKind === 'stab') { a = V.add(V.add(V.mad(SRp, cr, 0.12), V.mul(cf, 0.10)), V.mul(sd, -0.02)); b = V.add(V.mad(SRp, cf, 0.62), V.mul(cr, 0.02)); }
    else { a = V.add(V.add(V.mad(SRp, cr, 0.34), V.mul(cf, 0.22)), V.mul(sd, 0.10)); b = V.add(V.add(V.mad(SRp, cr, -0.30), V.mul(cf, 0.44)), V.mul(sd, -0.08)); }
    p.tR = q < 0.2 ? V.lerp(grip, a, sm01(q / 0.2)) : q < 0.34 ? V.lerp(a, b, sm01((q - 0.2) / 0.14)) : V.lerp(b, grip, sm01((q - 0.34) / 0.18));
  }
  p.fR = null;
  return p;
}
function lyingPose(c) {
  const dd = c.deathDir || [0, 0, -1];
  const g = c.y;
  const P = [c.x, g + 0.16, c.z];
  const up = [0, 1, 0];
  const C = [P[0] + dd[0] * 0.37, g + 0.17, P[2] + dd[2] * 0.37];
  const cf = [0, 1, 0], cu = dd, cr = V.cross(cf, cu);
  const H = [C[0] + dd[0] * 0.38, g + 0.14, C[2] + dd[2] * 0.38];
  const hf = V.norm([-dd[0] * 0.3 + cr[0] * 0.5, 0.8, -dd[2] * 0.3 + cr[2] * 0.5]);
  const hr = cr, hu = V.cross(hr, hf);
  const wf = V.norm([cr[0] * 0.8 + dd[0] * 0.3, 0.0, cr[2] * 0.8 + dd[2] * 0.3]);
  const wr = V.norm(V.cross(wf, up)), wu = V.cross(wr, wf);
  const W0 = [C[0] + cr[0] * 0.55 + dd[0] * 0.1, g + 0.07, C[2] + cr[2] * 0.55 + dd[2] * 0.1];
  const sp = c.splay || 0.3;
  return {
    P, pr: cr, pu: dd, pf: [0, 1, 0], C, cr, cu, cf, H, hr, hu, hf, W0, wr, wu, wf,
    tR: [C[0] + cr[0] * 0.5 + dd[0] * 0.2, g + 0.05, C[2] + cr[2] * 0.5 + dd[2] * 0.2],
    tL: [C[0] - cr[0] * (0.35 + sp) + dd[0] * 0.3, g + 0.05, C[2] - cr[2] * (0.35 + sp) + dd[2] * 0.3],
    polR: [0, 1, 0], polL: [0, 1, 0], kp: [0, 1, 0],
    fR: [P[0] - dd[0] * 0.85 + cr[0] * (0.20 + sp * 0.4), g + 0.08, P[2] - dd[2] * 0.85 + cr[2] * (0.20 + sp * 0.4)],
    fL: [P[0] - dd[0] * (0.8 + sp) - cr[0] * (0.2 + sp * 0.5), g + 0.08, P[2] - dd[2] * (0.8 + sp) - cr[2] * (0.2 + sp * 0.5)],
    R: cr, F: dd, SRoff: 0.20, lying: true,
  };
}
const POSE_V = ['P', 'pr', 'pu', 'pf', 'C', 'cr', 'cu', 'cf', 'H', 'hr', 'hu', 'hf', 'W0', 'wr', 'wu', 'wf', 'tR', 'tL', 'polR', 'polL', 'kp'];
function lerpPose(a, b, t) {
  const o = {};
  for (const k of POSE_V) o[k] = V.lerp(a[k], b[k], t);
  for (const k of ['pr', 'pu', 'pf', 'cr', 'cu', 'cf', 'hr', 'hu', 'hf', 'wr', 'wu', 'wf', 'polR', 'polL', 'kp']) o[k] = V.norm(o[k]);
  o.R = a.R; o.F = a.F; o.SRoff = 0.2; o.fR = b.fR; o.fL = b.fL; o.t = t;
  return o;
}

function makeRig(p, c) {
  const rig = { P: p.P, pr: p.pr, pu: p.pu, pf: p.pf, C: p.C, cr: p.cr, cu: p.cu, cf: p.cf, H: p.H, hr: p.hr, hu: p.hu, hf: p.hf, W0: p.W0, wr: p.wr, wu: p.wu, wf: p.wf, caps: [] };
  const so = p.SRoff;
  rig.SR = V.add(V.mad(p.C, p.cr, so), V.mul(p.cu, 0.15));
  rig.SL = V.add(V.mad(p.C, p.cr, -so), V.mul(p.cu, 0.15));
  const [ER, hR] = ik2(rig.SR, p.tR, ARM1, ARM2, p.polR);
  const [EL, hL] = ik2(rig.SL, p.tL, ARM1, ARM2, p.polL);
  rig.ER = ER; rig.hR = hR; rig.EL = EL; rig.hL = hL;
  const gb = p.lying ? null : gaitBody(c.gait, c.speed), hipUp = p.lying ? 0 : -0.04 + gb.bob, hs = gb ? -gb.sway : 0;
  rig.HR = V.add(V.mad(p.P, p.pr, 0.095 + hs), V.mul([0, 1, 0], hipUp));
  rig.HL = V.add(V.mad(p.P, p.pr, -0.095 + hs), V.mul([0, 1, 0], hipUp));
  let fR, fL;
  if (p.fR) { fR = p.fR; fL = p.fL; }
  else {
    const R = p.R, F = p.F;
    const sp = c.speed;
    const mx = c.lmx, mz = c.lmz;
    const foot = (side, ph, hurt) => {
      const gf = gaitFoot(ph, sp, hurt), off = gf.off, ly = gf.ly;
      const fx = c.x + R[0] * (0.11 * side + mx * off) + F[0] * mz * off, fz = c.z + R[2] * (0.11 * side + mx * off) + F[2] * mz * off;
      const onT = c.y <= World.H(c.x, c.z) + 0.3, fy = onT ? Math.max(World.H(fx, fz), c.y - 0.35) : c.y;
      return [fx, fy + 0.08 + ly, fz, gf.pitch];
    };
    fR = foot(1, c.gait, c.parts.rLeg.black); fL = foot(-1, c.gait + Math.PI, c.parts.lLeg.black);
  }
  const kpR = V.norm([p.kp[0] + p.pr[0] * 0.12, p.kp[1], p.kp[2] + p.pr[2] * 0.12]);
  const kpL = V.norm([p.kp[0] - p.pr[0] * 0.12, p.kp[1], p.kp[2] - p.pr[2] * 0.12]);
  const [KR, aR] = ik2(rig.HR, fR, LEG1, LEG2, kpR);
  const [KL, aL] = ik2(rig.HL, fL, LEG1, LEG2, kpL);
  rig.KR = KR; rig.aR = aR; rig.KL = KL; rig.aL = aL;
  rig.fpR = fR[3] || 0; rig.fpL = fL[3] || 0;
  rig.lying = !!p.lying;
  const cap = (part, a, b, r) => rig.caps.push({ part, a, b, r });
  cap('head', V.mad(p.H, p.hu, -0.02), V.mad(p.H, p.hu, 0.06), 0.118);
  cap('thorax', V.mad(p.C, p.cu, -0.13), V.mad(p.C, p.cu, 0.14), 0.175);
  cap('stomach', V.mad(p.P, p.pu, p.lying ? 0 : -0.02), V.mad(p.P, p.cu, 0.16), 0.165);
  cap('rArm', rig.SR, rig.ER, 0.055); cap('rArm', rig.ER, rig.hR, 0.05);
  cap('lArm', rig.SL, rig.EL, 0.055); cap('lArm', rig.EL, rig.hL, 0.05);
  cap('rLeg', rig.HR, rig.KR, 0.09); cap('rLeg', rig.KR, rig.aR, 0.07);
  cap('lLeg', rig.HL, rig.KL, 0.09); cap('lLeg', rig.KL, rig.aL, 0.07);
  return rig;
}

/* ---------- боец ---------- */
let _cid = 0;
class Combatant {
  constructor(o) {
    this.id = ++_cid; this.name = o.name || 'Боец'; this.team = o.team; this.isPlayer = !!o.isPlayer;
    this.x = o.x; this.y = o.y === undefined ? World.H(o.x, o.z) : o.y; this.z = o.z; this.vx = 0; this.vy = 0; this.vz = 0;
    this.yaw = o.yaw || 0; this.pitch = 0; this.leanA = 0; this.crouch = 0; this.h = 1.8;
    this.grounded = true; this.speed = 0; this.lmx = 0; this.lmz = 0; this.gait = 0; this.stepD = 0;
    this.stamina = 100; this.canSprint = true; this.sprinting = false; this.ads = 0; this.adsIn = false;
    this.parts = {};
    for (const p of PARTS) this.parts[p] = { hp: PART_MAX[p], max: PART_MAX[p], black: false, lb: false, hb: false, fx: false };
    this.armor = {};
    const set = ARMOR_SETS[o.armor === undefined ? 3 : o.armor];
    if (set) for (const k in set) this.armor[k] = { cls: set[k][0], dur: set[k][1], max: set[k][1], cov: set[k][2] };
    this.pain = 0; this.painkiller = 0; this.stun = 0; this.suppress = 0; this.hurtFlash = 0;
    this.alive = true; this.deathT = 0; this.deathDir = null; this.splay = rnd(0.1, 0.5);
    this.inv = o.inv || { bandage: 2, tourniquet: 1, splint: 1, pills: 1, medPool: 150 };
    if (this.inv.frag === undefined) this.inv.frag = 0; if (this.inv.flash === undefined) this.inv.flash = 0;
    this.weapons = [this.mkWeapon(o.primary || 'm4', o.mags === undefined ? 4 : o.mags), this.mkWeapon('glock', 3)];
    this.cur = 0; this.swapT = 0; this.swapTo = 0; this.fireT = 0; this.triggerHeld = false;
    this.reloadT = -1; this.reloadDur = 2; this.reloadKind = 'tac'; this.reloadFlags = {};
    this.healing = null; this.lowReady = 0.4; this.idleLow = 0.5; this.shake = 1; this.holdT = 0; this.gasp = 0; this.lastFireT = -9;
    this.swayP = 0; this.swayY = 0; this.wallLow = 0; this.punchP = 0; this.punchY = 0; this.kick = 0; this.recoilBuild = 0; this.hitKick = { p: 0, y: 0 };
    this.in = { mx: 0, mz: 0, sprint: false, crouch: false, fire: false, ads: false, lean: 0, jump: false, reload: false, switchTo: -1, breath: false, mode: false, throwStart: false, throwHeld: false, melee: false };
    this.throwT = -1; this.throwRel = false; this.throwRelT = 0; this.throwFuse = 0; this.throwHold = 0; this.throwSpeed = 0; this.nade = 'frag';
    this.meleeT = -1; this.meleeKind = 'slash'; this.meleeHit = false; this.meleeCd = 0; this.meleeAlt = false;
    this.blind = 0; this.blindMax = 1; this.deaf = 0; this.blast = null;
    this.stats = { kills: 0, headshots: 0, shots: 0, hits: 0, damage: 0 };
    this.eye = [this.x, 1.6, this.z]; this.sightDir = [0, 0, -1]; this.muzzle = [this.x, 1.4, this.z];
    this.aimDist = 50; this.lastShotAt = null; this.lastShotT = -99; this.lastHitBy = null; this.lastHitT = -99;
    this.t = 0; this.rig = null; this.hist = []; this.protT = 0; this.mT = -1;
    this.updateRig();
  }
  mkWeapon(id, mags) {
    const def = WEAPONS[id];
    return { def, mag: def.mag, chamber: 1, reserve: Array(mags).fill(def.mag), mode: def.modes[0], zeroI: def.zero0 };
  }
  get weapon() { return this.weapons[this.cur]; }
  totalHP() { let s = 0; for (const p of PARTS) s += this.parts[p].hp; return s; }
  totalMax() { return 440; }
  ammoReserve() { return this.weapon.reserve.reduce((a, b) => a + b, 0); }

  legFactor() {
    let m = 1; const pk = this.painkiller > 0;
    for (const s of ['lLeg', 'rLeg']) {
      const p = this.parts[s];
      if (p.black) m -= 0.42; else { if (p.fx) m -= pk ? 0.12 : 0.28; if (p.hp / p.max < 0.4) m -= 0.06; }
    }
    return Math.max(0.28, m);
  }
  update(dt) {
    this._dt = dt;
    if (!this.alive) { this.deathT += dt; if (!this.rag && this.rig && !Game.noRagdoll) this.startRagdoll(); if (this.rag || this.deathT < 1.6 || !this.rig) this.updateRig(); return; }
    this.t += dt;
    if (this.protT > 0) this.protT -= dt;
    if (this.netMode === 'proxy') { this.proxyStep(dt); this.updateRig(); return; }
    if (this.netMode === 'human') { this.humanStep(dt); if (this.alive) this.updateRig(); return; }
    this.statusTick(dt);
    if (!this.alive) { this.updateRig(); return; }
    this.movement(dt);
    this.weaponUpdate(dt);
    this.updateRig();
  }
  // сервер: игрок-человек — положение приходит от клиента, здесь только здоровье и ближний бой
  humanStep(dt) {
    if (!this.alive) return;
    this.statusTick(dt);
    if (!this.alive) return;
    if (this.healing) {
      this.healing.t += dt;
      if (this.healing.t >= this.healing.dur) this.finishHeal();
    }
    if (this.mT >= 0) { this.mT += dt; if (this.mT >= 0.2) { this.mT = -1; if (this.rig) { this.meleeKind = this.mKind; this.doMelee(); } } }
    // шаги для слуха ботов
    if (this.grounded && this.speed > 0.6) {
      this.stepD += this.speed * dt; const stride = this.sprinting ? 2.1 : this.crouch > 0.5 ? 1.0 : 1.45;
      if (this.stepD > stride) { this.stepD = 0; Bus.emit('step', { c: this, x: this.x, y: this.y, z: this.z, loud: this.sprinting ? 1 : this.crouch > 0.5 ? 0.18 : 0.5 }); }
    }
  }
  // клиент: чужой боец — состояние приходит из снапшотов
  proxyStep(dt) {
    if (this.grounded && this.speed > 0.6) {
      this.stepD += this.speed * dt; const stride = this.sprinting ? 2.1 : this.crouch > 0.5 ? 1.0 : 1.45;
      if (this.stepD > stride) { this.stepD = 0; Bus.emit('step', { c: this, x: this.x, y: this.y, z: this.z, loud: this.sprinting ? 1 : this.crouch > 0.5 ? 0.18 : 0.5 }); }
    }
  }
  histAt(lag) {
    const h = this.hist, tt = Game.time - lag;
    for (let i = h.length - 1; i >= 0; i--) if (h[i].t <= tt) return h[i];
    return h[0] || null;
  }
  statusTick(dt) {
    let bleed = 0;
    for (const p of PARTS) { const q = this.parts[p]; if (q.lb) bleed += 0.5; if (q.hb) bleed += 2.6; }
    if (bleed > 0 && Game.netClient) { this.bleeding = bleed; }
    else if (bleed > 0) {
      const live = PARTS.filter(p => p !== 'head' && this.parts[p].hp > 0);
      if (live.length) {
        const each = bleed * dt / live.length;
        for (const p of live) { const q = this.parts[p]; q.hp -= each; if (q.hp <= 0) { q.hp = 0; q.black = true; if (p === 'thorax') { this.die(null, 'thorax', null, 0, 'bleed'); return; } } }
      }
      this.bleeding = bleed;
    } else if (!Game.netClient) {
      this.bleeding = 0;
      for (const p of PARTS) { const q = this.parts[p]; if (!q.black && q.hp < q.max) q.hp = Math.min(q.max, q.hp + 0.035 * dt); }
    }
    this.pain = Math.max(0, this.pain - dt); this.painkiller = Math.max(0, this.painkiller - dt);
    this.stun = Math.max(0, this.stun - dt); this.suppress = Math.max(0, this.suppress - dt * 0.35);
    this.hurtFlash = Math.max(0, this.hurtFlash - dt * 1.8);
    if (this.blast) { this.vx += this.blast[0] * 0.5; this.vz += this.blast[2] * 0.5; if (this.grounded) this.vy = Math.max(this.vy, this.blast[1] * 0.6); this.blast = null; }
    this.gasp = Math.max(0, this.gasp - dt); this.blind = Math.max(0, this.blind - dt); this.deaf = Math.max(0, this.deaf - dt); this.meleeCd = Math.max(0, this.meleeCd - dt);
    // стабильность оружия
    let s = 1;
    for (const a of ['lArm', 'rArm']) {
      const q = this.parts[a];
      if (q.black) s *= 1.9; else { if (q.fx) s *= this.painkiller > 0 ? 1.25 : 1.6; if (q.hp / q.max < 0.5) s *= 1.15; }
    }
    if (this.pain > 0 && this.painkiller <= 0) s *= 1.3 + Math.min(this.pain, 10) * 0.03;
    if (this.stamina < 30) s *= 1 + (30 - this.stamina) / 55;
    if (this.stun > 0) s *= 1.6;
    if (this.in.breath && this.ads > 0.7 && this.holdT < 5 && this.gasp <= 0) { s *= 0.18; this.holdT += dt; if (this.holdT >= 5) { this.gasp = 2.2; } }
    else if (!this.in.breath) this.holdT = Math.max(0, this.holdT - dt * 1.5);
    if (this.gasp > 0) s *= 1.8;
    this.shake = s;
  }
  movement(dt) {
    const I = this.in, F = fwdVec(this.yaw, 0), R = [Math.cos(this.yaw), 0, -Math.sin(this.yaw)];
    let wantC = I.crouch;
    if (!wantC && this.crouch > 0.5 && World.blockedAt(this.x, this.y, this.z, 0.35, 1.8)) wantC = true;
    this.crouch = clamp(this.crouch + (wantC ? 1 : -1) * dt * 4.2, 0, 1);
    this.h = lerp(1.8, 1.25, this.crouch);
    this.leanA = damp(this.leanA, clamp(I.lean, -1, 1), 9, dt);
    const adsT = I.ads && this.swapT <= 0 && this.reloadT < 0 && !this.healing && !this.sprinting && this.throwT < 0 && this.meleeT < 0 ? 1 : 0;
    this.ads = clamp(this.ads + (adsT ? 1 : -1) * dt / Math.max(0.1, this.weapon.def.adsTime), 0, 1);
    const wants = I.mx !== 0 || I.mz !== 0;
    const leg = this.legFactor();
    let max = 3.3, spr = false;
    if (I.sprint && wants && I.mz > 0.2 && this.ads < 0.1 && this.crouch < 0.4 && this.canSprint && !this.healing && this.grounded && leg > 0.5 && this.parts.lLeg.black === false && this.parts.rLeg.black === false) { spr = true; max = 5.9; }
    if (this.crouch > 0.5) max = 1.8; else max = lerp(max, 1.8, this.crouch);
    if (this.ads > 0.5) max *= 0.55;
    if (this.healing) max *= 0.6;
    if (this.reloadT >= 0) max *= 0.85;
    max *= leg;
    if (this.stun > 0) max *= 0.8;
    this.sprinting = spr;
    if (spr) { this.stamina = Math.max(0, this.stamina - dt * 9 * (leg < 0.8 ? 1.5 : 1)); if (this.stamina <= 0) this.canSprint = false; }
    else { this.stamina = Math.min(100, this.stamina + dt * (wants ? 4 : 8) * (this.parts.thorax.hp < 25 ? 0.5 : 1)); if (this.stamina > 22) this.canSprint = true; }
    let wx = R[0] * I.mx + F[0] * I.mz, wz = R[2] * I.mx + F[2] * I.mz;
    const wl = Math.hypot(wx, wz); if (wl > 1) { wx /= wl; wz /= wl; }
    const tvx = wx * max, tvz = wz * max;
    const acc = this.grounded ? (spr ? 16 : 13) : 1.2;
    const k = Math.min(1, acc * dt);
    this.vx += (tvx - this.vx) * k; this.vz += (tvz - this.vz) * k;
    if (I.jump && this.grounded && this.stamina > 8 && this.crouch < 0.5 && leg > 0.55) { this.vy = 6.0; this.stamina -= 12; Bus.emit('jump', this); }
    I.jump = false;
    const r = 0.35, h = this.h;
    const nx = this.x + this.vx * dt, nz = this.z + this.vz * dt;
    if (!World.blockedAt(nx, this.y, this.z, r, h)) this.x = nx; else this.vx = 0;
    if (!World.blockedAt(this.x, this.y, nz, r, h)) this.z = nz; else this.vz = 0;
    this.vy -= 22 * dt;
    let ny = this.y + this.vy * dt;
    if (this.vy > 0 && World.ceilingAt(this.x, this.z, r, ny + h, this.vy * dt)) this.vy = 0, ny = this.y;
    this.y = ny;
    const gh = World.groundH(this.x, this.z, r, this.y + STEP + 0.05);
    const was = this.grounded;
    if (this.y <= gh + 0.001) {
      if (this.vy < -3 && !was) Bus.emit('land', { c: this, v: -this.vy });
      if (this.vy < -9.5) Combat.fallDamage(this, -this.vy);
      this.y = gh; this.vy = 0; this.grounded = true;
    } else this.grounded = false;
    this.speed = Math.hypot(this.vx, this.vz);
    if (this.speed > 0.3 && wants) { this.lmx = I.mx / (Math.hypot(I.mx, I.mz) || 1); this.lmz = I.mz / (Math.hypot(I.mx, I.mz) || 1); }
    this.gait += this.speed * dt * 4.2;
    if (this.grounded && this.speed > 0.6) {
      this.stepD += this.speed * dt;
      const stride = spr ? 2.1 : this.crouch > 0.5 ? 1.0 : 1.45;
      if (this.stepD > stride) { this.stepD = 0; Bus.emit('step', { c: this, x: this.x, y: this.y, z: this.z, loud: spr ? 1 : this.crouch > 0.5 ? 0.18 : 0.5 }); }
    }
    if (this.rig) {
      const rg = this.rig, h = World.ray(rg.W0[0], rg.W0[1], rg.W0[2], rg.wf[0], rg.wf[1], rg.wf[2], 0.6);
      this.wallLow = damp(this.wallLow, h ? clamp(1 - h.t / 0.6, 0, 1) * 1.1 : 0, 12, dt);
    }
    // низкая стойка оружия
    let low = 0;
    if (spr) low = 1; else if (this.healing) low = 1;
    else if (this.ads > 0.1 || this.t - this.lastFireT < 1.2) low = 0;
    else low = this.isPlayer ? 0.0 : this.idleLow;
    if (this.swapT > 0) low = Math.max(low, 0.9);
    if (this.throwT >= 0 || this.meleeT >= 0) low = Math.max(low, 0.85);
    low = Math.max(low, this.wallLow);
    this.lowReady = damp(this.lowReady, low, 8, dt);
  }
  weaponUpdate(dt) {
    const I = this.in;
    this.fireT -= dt;
    if (I.switchTo >= 0 && I.switchTo !== this.cur && this.swapT <= 0 && !this.healing) {
      this.swapTo = I.switchTo; this.swapT = 0.6; this.reloadT = -1; Bus.emit('swap', this);
    }
    I.switchTo = -1;
    if (this.swapT > 0) { this.swapT -= dt; if (this.swapTo !== this.cur && this.swapT < 0.3) { this.cur = this.swapTo; this.reloadT = -1; } }
    if (I.throwStart) { I.throwStart = false; this.startThrow(); }
    if (I.melee) { I.melee = false; this.startMelee(); }
    if (this.throwT >= 0) this.tickThrow(dt, I);
    if (this.meleeT >= 0) this.tickMelee(dt);
    const w = this.weapon, def = w.def;
    if (I.mode) { I.mode = false; if (def.modes.length > 1) { w.mode = def.modes[(def.modes.indexOf(w.mode) + 1) % def.modes.length]; Bus.emit('mode', this); } }
    if (this.healing) {
      this.healing.t += dt;
      if (I.fire || I.reload || this.swapT > 0) { this.healing = null; }
      else if (this.healing.t >= this.healing.dur) this.finishHeal();
    }
    // перезарядка
    if (I.reload && this.reloadT < 0 && this.swapT <= 0 && !this.healing && !this.sprinting && this.throwT < 0 && this.meleeT < 0) this.startReload();
    I.reload = false;
    if (this.reloadT >= 0) {
      this.reloadT += dt;
      const p = this.reloadT / this.reloadDur, f = this.reloadFlags;
      if (p > 0.2 && !f.out) { f.out = 1; Bus.emit('magout', this); }
      if (p > 0.62 && !f.swap) {
        f.swap = 1;
        let best = -1, bi = -1; w.reserve.forEach((m, i) => { if (m > best) { best = m; bi = i; } });
        if (bi >= 0 && best > 0) { const old = w.mag; w.mag = best; w.reserve.splice(bi, 1); if (old > 0) w.reserve.push(old); }
        Bus.emit('magin', this);
      }
      if (p > 0.88 && this.reloadKind === 'empty' && !f.rack) { f.rack = 1; if (w.mag > 0) { w.mag--; w.chamber = 1; } Bus.emit('rack', this); }
      if (this.reloadT >= this.reloadDur) { if (w.chamber < 1 && w.mag > 0) { w.mag--; w.chamber = 1; } this.reloadT = -1; }
    }
    // выстрел
    const ready = this.swapT <= 0 && this.reloadT < 0 && !this.healing && !this.sprinting && this.throwT < 0 && this.meleeT < 0;
    if (I.fire && ready && this.fireT <= 0) {
      if (!(w.mode === 'semi' && this.triggerHeld)) {
        if (w.chamber > 0) this.shoot();
        else if (!this.triggerHeld) { this.fireT = 0.2; Bus.emit('dry', this); }
      }
    }
    this.triggerHeld = I.fire;
    // отдача затухает
    this.punchP = damp(this.punchP, 0, 7.5, dt); this.punchY = damp(this.punchY, 0, 7.5, dt);
    this.kick = damp(this.kick, 0, 13, dt); this.recoilBuild = Math.max(0, this.recoilBuild - dt * 3);
    this.hitKick.p = damp(this.hitKick.p, 0, 9, dt); this.hitKick.y = damp(this.hitKick.y, 0, 9, dt);
  }
  startReload() {
    const w = this.weapon;
    if (w.reserve.length === 0 || Math.max(...w.reserve) <= 0) return false;
    if (w.mag >= w.def.mag && w.chamber > 0) return false;
    this.reloadKind = w.chamber > 0 || w.mag > 0 ? 'tac' : 'empty';
    if (w.chamber <= 0) this.reloadKind = 'empty';
    this.reloadDur = w.def.reload[this.reloadKind]; this.reloadT = 0; this.reloadFlags = {};
    this.in.ads = this.in.ads; Bus.emit('reload', this);
    return true;
  }
  shoot() {
    const w = this.weapon, def = w.def, cart = CART[def.cart];
    w.chamber = 0; if (w.mag > 0) { w.mag--; w.chamber = 1; }
    this.fireT = 60 / def.rpm; this.lastFireT = this.t;
    const rg = this.rig, eye = rg.W0, sdir = rg.wf, muz = V.add(V.mad(rg.W0, rg.wu, -def.sightH), V.mul(rg.wf, def.muzzleZ));
    const Z = this.isPlayer ? def.zeroSteps[w.zeroI] : clamp(this.aimDist, 12, 400);
    const zp = [eye[0] + sdir[0] * Z, eye[1] + sdir[1] * Z + dropAt(cart, Z) - Z * ((def.zeroBias || 0) + (this.isPlayer ? (Game.zeroAdj || 0) : 0)), eye[2] + sdir[2] * Z];
    let d = V.norm(V.sub(zp, muz));
    const moa = def.moa * 0.000291;
    let ang = moa * this.shake + (1 - this.ads) * (this.isPlayer ? 0.014 : 0.006) + this.speed * 0.0014 + this.recoilBuild * 0.0035;
    if (this.suppress > 0.4) ang *= 1 + this.suppress;
    const rr = ang * Math.sqrt(Math.random()), th = Math.random() * Math.PI * 2;
    const up = Math.abs(d[1]) > 0.95 ? [1, 0, 0] : [0, 1, 0];
    const rt = V.norm(V.cross(d, up)), u2 = V.cross(rt, d);
    d = V.norm(V.add(d, V.add(V.mul(rt, Math.cos(th) * rr), V.mul(u2, Math.sin(th) * rr))));
    // дуло в стене — пуля стартует от точки упора
    let origin = muz;
    const ex = muz[0] - eye[0], ey = muz[1] - eye[1], ez = muz[2] - eye[2], el = Math.hypot(ex, ey, ez);
    if (el > 0.01) { const bh = World.ray(eye[0], eye[1], eye[2], ex / el, ey / el, ez / el, el); if (bh) origin = [eye[0] + ex / el * (bh.t - 0.03), eye[1] + ey / el * (bh.t - 0.03), eye[2] + ez / el * (bh.t - 0.03)]; }
    this.shotCount = (this.shotCount || 0) + 1;
    Ballistics.spawn(this, cart, origin, d, this.shotCount % 4 === 0, Game.netClient ? { cos: true } : undefined);
    if (Game.netClient && this.isPlayer) Bus.emit('netShot', { p: origin, d, wi: this.cur, tr: this.shotCount % 4 === 0 });
    this.stats.shots++;
    // отдача
    const sc = (this.shake > 1 ? 1 + (this.shake - 1) * 0.3 : 1) * (this.ads > 0.5 ? 0.85 : 1.1);
    const rv = def.recV * rnd(0.75, 1.25) * sc, rh = def.recH * rnd(-1, 1) * sc;
    this.punchP += rv * 0.65; this.punchY += rh * 0.7;
    this.pitch += rv * 0.35; this.yaw += rh * 0.3;
    this.kick = Math.min(1.2, this.kick + 0.6); this.recoilBuild = Math.min(1, this.recoilBuild + 0.1);
    Bus.emit('shot', { c: this, pos: muz, dir: d, def, cart, tr: this.shotCount % 4 === 0 });
    Bus.emit('eject', { c: this, def });
  }
  /* ----- лечение ----- */
  autoTarget(type) {
    if (type === 'bandage') return PARTS.find(p => this.parts[p].lb) || null;
    if (type === 'tourniquet') return PARTS.find(p => this.parts[p].hb) || null;
    if (type === 'splint') return PARTS.find(p => this.parts[p].fx) || null;
    if (type === 'pills') return 'any';
    if (type === 'medkit') {
      let best = null, bs = 1;
      for (const p of PARTS) { const q = this.parts[p]; if (q.black || q.hp >= q.max - 0.5) continue; const f = q.hp / q.max; if (f < bs) { bs = f; best = p; } }
      if (best) return best;
      return PARTS.find(p => this.parts[p].black) || null;
    }
    return null;
  }
  canUse(type) {
    if (type === 'medkit') return this.inv.medPool > 0;
    return (this.inv[type] || 0) > 0;
  }
  startHeal(type, part) {
    if (!this.alive || this.healing || !this.canUse(type) || this.reloadT >= 0) return false;
    if (!part) part = this.autoTarget(type);
    if (!part) return false;
    if (type === 'pills' && this.painkiller > 30) return false;
    this.healing = { type, part, t: 0, dur: ITEMS[type].t };
    if (Game.netClient) Bus.emit('netHeal', { type, part });
    Bus.emit('healstart', { c: this, type });
    return true;
  }
  finishHeal() {
    const h = this.healing; this.healing = null;
    if (Game.netClient) { Bus.emit('healdone', { c: this, type: h.type }); return; }
    const q = this.parts[h.part], inv = this.inv;
    if (h.type === 'bandage') { if (q && q.lb) { q.lb = false; inv.bandage--; } }
    else if (h.type === 'tourniquet') { if (q && q.hb) { q.hb = false; inv.tourniquet--; } }
    else if (h.type === 'splint') { if (q && q.fx) { q.fx = false; inv.splint--; } }
    else if (h.type === 'pills') { this.painkiller = 150; this.pain = 0; inv.pills--; }
    else if (h.type === 'medkit' && q) {
      if (q.black) { const cost = Math.min(inv.medPool, 60); q.black = false; q.hp = Math.min(q.max, q.max * 0.25 * (cost / 60)); inv.medPool -= cost; }
      else { const heal = Math.min(inv.medPool, q.max - q.hp, 70); q.hp += heal; inv.medPool -= heal; }
      q.lb = false;
    }
    Bus.emit('healdone', { c: this, type: h.type });
  }
  die(attacker, part, bullet, dist, cause) {
    if (!this.alive) return;
    this.alive = false; this.deathT = 0; this.healing = null; this.reloadT = -1; this.deathPart = part;
    if (!this.deathDir) { const f = fwdVec(this.yaw, 0); this.deathDir = V.norm([-f[0], 0, -f[2]]); }
    this.in = { mx: 0, mz: 0, sprint: false, crouch: false, fire: false, ads: false, lean: 0, jump: false, reload: false, switchTo: -1, breath: false, mode: false, throwStart: false, throwHeld: false, melee: false };
    this.throwT = -1; this.throwRel = false; this.meleeT = -1;
    if (attacker && attacker !== this) { attacker.stats.kills++; if (part === 'head') attacker.stats.headshots++; }
    Bus.emit('death', { victim: this, attacker, part, bullet, dist, cause });
  }
  updateRig() {
    if (!this.alive && this.rag) {
      this.rag.step(this._dt || 1 / 60, this.rag.t < this.rag.muscleT ? this.ragTarget() : null);
      this.rig = this.rag.rig(this); return;
    }
    const st = standPose(this);
    let pose = st;
    if (!this.alive) {
      const t = sm01(this.deathT / 0.65), lp = lyingPose(this);
      if (t >= 1) pose = lp;
      else { pose = lerpPose(st, lp, t); if (t < 0.5) { pose.fR = null; pose.fL = null; } }
    }
    this.rig = makeRig(pose, this);
    if (!this.alive) this.rig.caps = [];
  }
}

/* ---------- боевая система ---------- */
const Combat = {
  fallDamage(c, v) {
    if (Game.netClient) { Bus.emit('netFall', { v }); return; }
    const d = (v - 9.5) * 9;
    for (const s of ['lLeg', 'rLeg']) { const q = c.parts[s]; q.hp = Math.max(0, q.hp - d * 0.7); if (q.hp <= 0) q.black = true; else if (d > 14 && Math.random() < 0.55) q.fx = true; }
    c.pain = Math.min(30, c.pain + 6); c.hurtFlash = 0.6;
    Bus.emit('fall', { c, d });
  },
  spread(victim, exclude, amount) {
    const live = PARTS.filter(p => p !== 'head' && p !== exclude && victim.parts[p].hp > 0);
    if (!live.length || amount <= 0) return;
    const each = amount / live.length;
    for (const p of live) {
      const q = victim.parts[p]; q.hp -= each;
      if (q.hp <= 0) { q.hp = 0; q.black = true; if (p === 'thorax') victim.pendingDeath = 'thorax'; }
    }
  },
  hitCombatant(v, part, b, point, dir) {
    const cart = b.cart, att = b.owner;
    if (v.protT > 0 || !v.alive) return { victim: v, attacker: att, part, dmg: 0, killed: false, blocked: true, penetrated: false, armorHit: false, pos: point, dir, dist: 0, cart };
    { const E = cart.v ? 0.5 * cart.mass * cart.v * cart.v : (cart === CART.knife ? 200 : 650); (v.hitLog || (v.hitLog = [])).push({ t: Game.time, part, dir: [dir[0], dir[1], dir[2]], dv: clamp(E / 1700 * 4.2, 0.8, 6) }); if (v.hitLog.length > 8) v.hitLog.shift(); }
    let dmg = cart.dmg * b.dmgScale, penetrated = true, armorHit = false, blocked = false;
    const ar = v.armor[part];
    if (ar && ar.dur > 0 && Math.random() < ar.cov) {
      armorHit = true;
      const eff = ar.cls * 10 * (0.55 + 0.45 * ar.dur / ar.max);
      const chance = clamp(0.5 + (b.pen - eff) / 30, 0.02, 0.99);
      if (Math.random() < chance) { dmg *= 0.82; ar.dur = Math.max(0, ar.dur - (0.6 + cart.dmg * 0.02)); }
      else { blocked = true; penetrated = false; dmg *= BLUNT[ar.cls]; ar.dur = Math.max(0, ar.dur - (1.2 + cart.dmg * 0.05)); }
    }
    const raw = dmg;
    dmg *= PART_MUL[part];
    const P = v.parts[part];
    let applied = 0, killed = false;
    if (P.hp > 0) {
      const real = Math.min(P.hp, dmg); P.hp -= real; applied = real;
      const over = dmg - real;
      if (P.hp <= 0.001) { P.hp = 0; P.black = true; if (part === 'head' || part === 'thorax') killed = true; else Combat.spread(v, part, over * 0.5); }
    } else { applied = dmg * 0.6; Combat.spread(v, part, applied); }
    if (v.pendingDeath) { killed = true; v.pendingDeath = null; }
    // состояния
    if (penetrated) {
      if (!P.hb && Math.random() < BLEED_H[part]) P.hb = true;
      else if (!P.lb && !P.hb && Math.random() < BLEED_L[part]) P.lb = true;
    }
    const limb = part.endsWith('Arm') || part.endsWith('Leg');
    if (limb && raw >= 14 && !P.fx && Math.random() < 0.16 + raw / 160) P.fx = true;
    if (limb || part === 'stomach') v.pain = Math.min(30, v.pain + 2 + applied * 0.16);
    if (part === 'head') v.stun = Math.min(4.5, v.stun + 0.8 + raw * 0.05);
    else if (blocked && part === 'thorax') v.stun = Math.min(1.5, v.stun + 0.25);
    v.hurtFlash = Math.min(1, v.hurtFlash + 0.4 + applied / 60);
    v.hitKick.p += rnd(-0.03, 0.05) * (1 + applied / 40); v.hitKick.y += rnd(-0.06, 0.06) * (1 + applied / 40);
    v.lastHitBy = att; v.lastHitT = Game.time;
    if (att) { att.stats.hits++; att.stats.damage += applied; }
    const dist = att ? Math.hypot(att.x - v.x, att.z - v.z) : 0;
    const info = { victim: v, attacker: att, part, dmg: applied, penetrated, blocked, armorHit, killed, pos: point, dir, dist, cart };
    if (!v.dmgDir) v.dmgDir = [0, 0, 0];
    v.deathDir = V.norm([dir[0], 0, dir[2]]);
    Bus.emit('hit', info);
    if (killed) v.die(att, part, b, dist);
    return info;
  },
};

if (typeof module !== 'undefined') module.exports = { Combatant, Combat, PARTS, PART_MAX, PART_RU, ITEMS, ik2 };

/* --- 35_nades.js --- */
/* ===== Гранаты (осколочная, светошумовая) и ближний бой ===== */
CART.knife = { name: 'Нож', dmg: 42, pen: 9, v: 0, mass: 0.1, cal: 0.01, cd: 0.3, k: 0 };
CART.frag = { name: 'Осколок', dmg: 40, pen: 15, v: 0, mass: 0.003, cal: 0.005, cd: 0.3, k: 0 };
const GREN = {
  frag: { ru: 'Осколочная', short: 'ОГ', fuse: 3.6 },
  flash: { ru: 'Светошумовая', short: 'СШ', fuse: 2.4 },
};
const FRAG_R = 15, FLASH_R = 20;

const Grenades = {
  list: [], nid: 0,
  reset() { this.list = []; },
  spawn(owner, kind, pos, vel, fuse) {
    const g = { id: ++this.nid, owner, kind, x: pos[0], y: pos[1], z: pos[2], vx: vel[0], vy: vel[1], vz: vel[2], fuse, t: 0, rest: 0, stopped: false, rot: 0 };
    this.list.push(g); return g;
  },
  update(dt) {
    for (let i = this.list.length - 1; i >= 0; i--) {
      const g = this.list[i];
      g.t += dt; g.fuse -= dt;
      if (g.fuse <= 0) { if (Game.netClient) { g.stale = (g.stale || 0) + dt; if (g.stale > 1.2) this.list.splice(i, 1); continue; } this.list.splice(i, 1); this.explode(g); continue; }
      if (g.stopped) continue;
      g.vy -= G * dt; const dmp = Math.max(0, 1 - 0.25 * dt); g.vx *= dmp; g.vz *= dmp;
      const mx = g.vx * dt, my = g.vy * dt, mz = g.vz * dt, len = Math.hypot(mx, my, mz);
      if (len > 1e-6) {
        const R = 0.07, dx = mx / len, dy = my / len, dz = mz / len;
        const h = World.ray(g.x, g.y, g.z, dx, dy, dz, len + R);
        if (h && h.t <= len + R) {
          const mt = h.box.mat, e = mt === 'metal' ? 0.45 : mt === 'wood' ? 0.3 : mt === 'dirt' ? 0.16 : 0.36;
          const th = Math.max(0, h.t - R); g.x += dx * th; g.y += dy * th; g.z += dz * th;
          const vn = g.vx * h.nx + g.vy * h.ny + g.vz * h.nz;
          if (vn < 0) {
            g.vx -= (1 + e) * vn * h.nx; g.vy -= (1 + e) * vn * h.ny; g.vz -= (1 + e) * vn * h.nz;
            const nv = g.vx * h.nx + g.vy * h.ny + g.vz * h.nz;
            const tx = g.vx - nv * h.nx, ty = g.vy - nv * h.ny, tz = g.vz - nv * h.nz;
            g.vx = nv * h.nx + tx * 0.74; g.vy = nv * h.ny + ty * 0.74; g.vz = nv * h.nz + tz * 0.74;
            if (-vn > 1.5) Bus.emit('nadebounce', { g, v: -vn, mat: mt });
          }
          if (h.ny > 0.5 && Math.hypot(g.vx, g.vy, g.vz) < 1.3) { g.vx = g.vy = g.vz = 0; g.stopped = true; }
          g.y += h.ny * 0.01;
        } else { g.x += mx; g.y += my; g.z += mz; }
      }
      g.x = clamp(g.x, -118.5, 118.5); g.z = clamp(g.z, -118.5, 118.5);
      const gy = World.H(g.x, g.z); if (g.y < gy + 0.04 && g.vy <= 0) { g.y = gy + 0.04; if (g.vy < -1.5) { g.vy *= -0.2; g.vx *= 0.7; g.vz *= 0.7; } else { g.vx *= 0.6; g.vz *= 0.6; g.vy = 0; if (Math.hypot(g.vx, g.vz) < 0.6) g.stopped = true; } }
      g.rot += Math.hypot(g.vx, g.vz) * dt * 3;
    }
  },
  explode(g) {
    const o = [g.x, g.y + 0.12, g.z];
    Bus.emit('explode', { x: g.x, y: g.y, z: g.z, kind: g.kind, owner: g.owner });
    if (g.kind === 'flash') { this.flashBang(o, g.owner); return; }
    const W = { head: 0.07, thorax: 0.30, stomach: 0.16, lArm: 0.12, rArm: 0.12, lLeg: 0.115, rLeg: 0.115 };
    for (const c of Game.combatants) {
      if (!c.alive || !c.rig) continue;
      if (Game.noFF && g.owner && c !== g.owner && c.team === g.owner.team) continue;
      if (c.protT > 0) continue;
      const r = c.rig, ctr = r.C, d = V.dist(o, ctr);
      if (d > FRAG_R) continue;
      // открытость цели: головa, грудь, таз
      const pts = [r.H, r.C, r.P];
      let vis = 0; for (const q of pts) if (World.los(o, q)) vis++;
      vis /= 3;
      const k = Math.pow(1 - d / FRAG_R, 1.3);
      let n = 9.5 * k * (vis + (d < 3 ? 0.3 : 0.04));
      // ударная волна ближе 6 м
      if (d < 6) { c.stun = Math.min(3.5, c.stun + (1 - d / 6) * 2.5); c.suppress = 1; c.deaf = Math.max(c.deaf || 0, 4 * (1 - d / 6) + 1); Bus.emit('blast', { c, d }); }
      const push = V.norm(V.sub(ctr, o)); const imp = 7 * Math.pow(1 - d / FRAG_R, 1.2) * (0.5 + vis * 0.5);
      c.blast = [push[0] * imp, Math.abs(push[1]) * imp * 0.7 + 1.2 * imp * 0.3, push[2] * imp];
      let cnt = Math.floor(n) + (Math.random() < n - Math.floor(n) ? 1 : 0);
      for (let i = 0; i < cnt && c.alive; i++) {
        let rr = Math.random(), part = 'thorax'; for (const p of PARTS) { rr -= W[p]; if (rr <= 0) { part = p; break; } }
        const pt = part === 'head' ? r.H : part === 'thorax' ? r.C : part === 'stomach' ? r.P : part === 'lArm' ? r.EL : part === 'rArm' ? r.ER : part === 'lLeg' ? r.KL : r.KR;
        const pb = { cart: CART.frag, owner: g.owner, dmgScale: rnd(0.75, 1.25), pen: CART.frag.pen * rnd(0.7, 1.3) };
        Combat.hitCombatant(c, part, pb, pt, V.norm(V.sub(pt, o)));
      }
    }
  },
  flashBang(o, owner) {
    for (const c of Game.combatants) {
      if (!c.alive || !c.rig) continue;
      const r = c.rig, d = V.dist(o, r.H);
      if (d > FLASH_R) continue;
      const seen = World.los(o, r.H);
      if (!seen && d > 3) continue;
      const to = V.norm(V.sub(o, r.H)), look = r.hf, face = clamp((V.dot(to, look) + 0.25) / 1.25, 0.12, 1);
      const f = (1 - d / FLASH_R) * (seen ? 1 : 0.35);
      const t = (1.2 + 5.8 * f) * (0.35 + 0.65 * face);
      c.blind = Math.max(c.blind || 0, t); c.blindMax = Math.max(c.blindMax || 1, t);
      c.deaf = Math.max(c.deaf || 0, 2 + 5 * f); c.stun = Math.min(4.5, (c.stun || 0) + f * 1.6);
      Bus.emit('blast', { c, d, flash: true });
    }
  },
};

/* ---------- методы бойца ---------- */
const CP = Combatant.prototype;
CP.canThrow = function () { return this.alive && this.throwT < 0 && this.meleeT < 0 && this.swapT <= 0 && (this.inv[this.nade] || 0) > 0; };
CP.startThrow = function () {
  if (!this.canThrow()) return false;
  this.throwT = 0; this.throwRel = false; this.throwFuse = GREN[this.nade].fuse; this.reloadT = -1; this.healing = null;
  Bus.emit('pin', this);
  return true;
};
CP.tickThrow = function (dt, I) {
  this.throwT += dt;
  if (!this.throwRel) {
    this.throwFuse -= dt;
    this.throwHold = (this.throwHold || 0) + (this.throwT >= 0.4 ? dt : 0);
    if (this.throwT >= 0.4) {
      this.throwT = 0.4;
      if (!I.throwHeld || this.throwHold > 3.2) { this.throwHold = 0; this.releaseNade(); }
    }
    if (this.throwFuse <= 0.04 && !this.throwRel) {
      // передержал: взрыв в руке
      const r = this.rig, k = this.nade; this.inv[k] = Math.max(0, (this.inv[k] || 0) - 1);
      this.throwT = -1; this.throwHold = 0;
      if (Game.netClient) Bus.emit('netThrow', { k, pos: r.hR, vel: [0, 0, 0], fuse: 0.03 });
      else Grenades.explode({ kind: k, x: r.hR[0], y: r.hR[1], z: r.hR[2], owner: this });
    }
  } else if (this.throwT - this.throwRelT > 0.5) { this.throwT = -1; this.throwRel = false; }
};
CP.releaseNade = function () {
  const k = this.nade;
  this.throwRel = true; this.throwRelT = this.throwT;
  this.inv[k] = Math.max(0, (this.inv[k] || 0) - 1);
  Bus.emit('throw', this);
  const r = this.rig, from = r.H, to = r.hR, d = V.sub(to, from), L = V.len(d);
  let pos = [to[0], to[1], to[2]];
  if (L > 0.01) { const h = World.ray(from[0], from[1], from[2], d[0] / L, d[1] / L, d[2] / L, L); if (h) pos = V.mad(from, d, Math.max(0, h.t - 0.12) / L); }
  const sp = this.throwSpeed || (this.in.crouch ? 8.5 : 16.5);
  const dir = fwdVec(this.yaw, this.pitch + 0.16);
  const vel = [dir[0] * sp + this.vx * 0.7, dir[1] * sp, dir[2] * sp + this.vz * 0.7];
  if (Game.netClient) Bus.emit('netThrow', { k, pos, vel, fuse: Math.max(0.35, this.throwFuse) });
  else Grenades.spawn(this, k, pos, vel, Math.max(0.35, this.throwFuse));
  this.throwSpeed = 0;
};
CP.cycleNade = function () {
  const ks = Object.keys(GREN); this.nade = ks[(ks.indexOf(this.nade) + 1) % ks.length];
  return this.nade;
};
CP.canMelee = function () { return this.alive && this.meleeT < 0 && this.throwT < 0 && this.swapT <= 0 && !this.healing && this.meleeCd <= 0; };
CP.startMelee = function () {
  if (!this.canMelee()) return false;
  this.meleeT = 0; this.meleeHit = false; this.reloadT = -1;
  this.meleeKind = (this.sprinting || this.speed > 4.2 || this.pitch < -0.35) ? 'stab' : (this.meleeAlt = !this.meleeAlt) ? 'slash' : 'stab';
  Bus.emit('meleestart', this);
  if (Game.netClient) Bus.emit('netMelee', { kind: this.meleeKind });
  return true;
};
CP.tickMelee = function (dt) {
  this.meleeT += dt;
  if (!this.meleeHit && this.meleeT >= 0.2) { this.meleeHit = true; this.doMelee(); }
  if (this.meleeT >= 0.52) { this.meleeT = -1; this.meleeCd = 0.25; }
};
CP.doMelee = function () {
  if (Game.netClient) return;
  const eye = this.rig.H, stab = this.meleeKind === 'stab', range = stab ? 2.05 : 1.8;
  const offs = stab ? [0, 0.07, -0.07] : [-0.6, -0.4, -0.2, 0, 0.2, 0.4, 0.6];
  let best = null;
  for (const off of offs) {
    const dir = fwdVec(this.yaw + off, this.pitch);
    const wh = World.ray(eye[0], eye[1], eye[2], dir[0], dir[1], dir[2], range), lim = wh ? wh.t : range;
    for (const v of Game.combatants) {
      if (v === this || !v.alive || !v.rig || v.team === this.team) continue;
      if (Math.hypot(v.x - this.x, v.z - this.z) > range + 0.6) continue;
      for (const cap of v.rig.caps) {
        const t = rayCapsule(eye[0], eye[1], eye[2], dir[0], dir[1], dir[2], lim, cap.a, cap.b, cap.r + 0.07);
        if (t >= 0 && t < lim && (!best || t < best.t)) best = { t, v, part: cap.part, dir };
      }
    }
  }
  if (!best) { Bus.emit('meleemiss', this); return; }
  const v = best.v, p = V.mad(eye, best.dir, best.t);
  const vf = fwdVec(v.yaw, 0), back = V.dot(vf, best.dir) > 0.4;
  const pb = { cart: CART.knife, owner: this, dmgScale: (stab ? 1.5 : 1) * (back ? 2.0 : 1) * rnd(0.9, 1.1), pen: CART.knife.pen };
  Bus.emit('meleehit', { c: this, v, part: best.part });
  Combat.hitCombatant(v, best.part, pb, p, best.dir);
};

if (typeof module !== 'undefined') module.exports = { Grenades, GREN };

/* --- 40_ai.js --- */
/* ===== ИИ ботов: восприятие, укрытия, бой, лечение ===== */
const DIFFS = [
  { n: 'Новичок', skill: 0.35, react: 0.95, aim: 3.2 },
  { n: 'Бывалый', skill: 0.55, react: 0.62, aim: 5.0 },
  { n: 'Профи', skill: 0.78, react: 0.40, aim: 7.5 },
  { n: 'Ветеран', skill: 0.95, react: 0.27, aim: 10 },
];
const CALLSIGNS = ['Волк', 'Рысь', 'Тень', 'Кобра', 'Ястреб', 'Орёл', 'Барс', 'Сокол', 'Медведь', 'Лис', 'Гром', 'Ворон', 'Кречет', 'Шторм'];

class Brain {
  constructor(c, d) {
    this.c = c; this.d = d; this.state = 'patrol';
    this.path = null; this.pi = 0; this.pathAge = 0; this.goal = null; this.wait = rnd(0.5, 3);
    this.target = null; this.vis = {}; this.lastSeenPos = null; this.lastSeenT = -99; this.targetVisible = false; this.acqT = 0;
    this.heard = null; this.strafe = 1; this.strafeT = 0; this.burstT = 0; this.pauseT = rnd(0.2, 0.6);
    this.aimErr = [0, 0]; this.aimErrT = 0; this.coverPos = null; this.coverT = 0; this.perceiveT = rnd(0, 0.12);
    this.stuckT = 0; this.lastPos = [c.x, c.z]; this.stuckCheck = 0; this.crouchT = 0; this.scan = rnd(0, 6);
    this.healCheck = 0; this.patrolYaw = c.yaw; this.sprintOK = Math.random() < 0.5;
  }
  enemies() {
    const c = this.c, out = [];
    for (const e of Game.combatants) if (e !== c && e.alive && e.team !== c.team) out.push(e);
    return out;
  }
  hear(x, z, dist, kind, y) {
    if (this.targetVisible) return;
    const err = dist * 0.05;
    this.heard = { x: x + rnd(-err, err), z: z + rnd(-err, err), y: y === undefined ? this.c.y : y, t: Game.time, kind };
  }
  perceive(dt) {
    const c = this.c, now = Game.time;
    this.perceiveT -= dt;
    if (this.perceiveT > 0) return;
    this.perceiveT = 0.12;
    const eye = c.rig.H, af = c.rig.wf;
    let best = null, bd = 1e9;
    for (const e of this.enemies()) {
      const dx = e.x - c.x, dz = e.z - c.z, dist = Math.hypot(dx, dz);
      if (dist > 170) { this.vis[e.id] = 0; continue; }
      const ch = e.rig.C, hd = e.rig.H;
      const dir = V.norm([ch[0] - eye[0], ch[1] - eye[1], ch[2] - eye[2]]);
      const fov = V.dot(dir, [af[0], 0, af[2]].map(v => v / (Math.hypot(af[0], af[2]) || 1)));
      const inFov = fov > 0.35 || dist < 6 || (this.state === 'combat' && fov > -0.2);
      let see = false;
      if (inFov) see = World.los(eye, ch) || World.los(eye, hd);
      if (see) {
        const mod = (1 + dist / 70) * (e.crouch > 0.5 ? 1.35 : 1) * (e.speed > 3 ? 0.8 : 1) * (e.ads > 0.5 ? 1.15 : 1);
        this.vis[e.id] = (this.vis[e.id] || 0) + 0.12;
        if (this.vis[e.id] >= this.d.react * mod * (this.target === e ? 0.3 : 1)) { if (dist < bd) { bd = dist; best = e; } }
      } else this.vis[e.id] = Math.max(0, (this.vis[e.id] || 0) - 0.08);
    }
    if (best) {
      if (this.target !== best || !this.targetVisible) this.acqT = now;
      this.target = best; this.targetVisible = true; this.lastSeenPos = [best.x, best.z, best.y]; this.lastSeenT = now;
    } else {
      this.targetVisible = false;
      if (c.lastHitBy && c.lastHitBy.alive && c.lastHitBy.team !== c.team && now - c.lastHitT < 1.5 && !this.target) {
        this.target = c.lastHitBy; this.lastSeenPos = [this.target.x, this.target.z, this.target.y]; this.lastSeenT = now - 0.5;
      }
    }
    if (this.target && !this.target.alive) { this.target = null; this.targetVisible = false; }
    if (this.target && now - this.lastSeenT > 14) this.target = null;
    if (c.lastShotAt && now - c.lastShotT < 1 && !this.target && !this.heard) this.heard = { x: c.lastShotAt[0], z: c.lastShotAt[1], y: c.y, t: now, kind: 'fire' };
  }
  think(dt) {
    const c = this.c; if (!c.alive || !c.rig) return;
    const now = Game.time, I = c.in, def = c.weapon.def;
    this.perceive(dt);
    I.fire = false; I.ads = false; I.sprint = false; I.mx = 0; I.mz = 0; I.crouch = false; I.lean = 0;
    const tgt = this.target;
    const engaged = !!tgt && (this.targetVisible || now - this.lastSeenT < 2.5);
    c.idleLow = engaged ? 0 : 0.55;
    // ---- перезарядка / смена оружия ----
    const w = c.weapon;
    const empty = w.mag <= 0 && w.chamber <= 0;
    const reserve = w.reserve.reduce((a, b) => a + b, 0);
    if (empty && reserve <= 0 && c.cur === 0 && c.weapons[1].mag + c.weapons[1].chamber > 0) I.switchTo = 1;
    else if (c.reloadT < 0 && c.swapT <= 0 && reserve > 0 && (empty || (!this.targetVisible && w.mag < 10 && w.mag < def.mag * 0.4))) I.reload = true;
    // ---- лечение вне боя ----
    this.healCheck -= dt;
    if (!c.healing && this.healCheck <= 0 && now - this.lastSeenT > 3.5 && now - c.lastHitT > 3 && c.reloadT < 0) {
      this.healCheck = 1.2;
      const p = c.parts;
      if (PARTS.some(k => p[k].hb) && c.startHeal('tourniquet')) {}
      else if (PARTS.some(k => p[k].lb) && c.startHeal('bandage')) {}
      else if ((p.lLeg.fx || p.rLeg.fx) && c.startHeal('splint')) {}
      else if (PARTS.some(k => !p[k].black && p[k].hp < p[k].max * 0.5) && c.startHeal('medkit')) {}
      else if (c.pain > 4 && c.painkiller <= 0 && c.startHeal('pills')) {}
    }
    if (c.healing) { this.faceHeading(dt, 1.5); return; }
    // ---- гранаты: ослеплён / бросок / уклонение ----
    this.nadeCd = (this.nadeCd === undefined ? rnd(6, 18) : this.nadeCd) - dt;
    if (c.blind > 0.4) { I.crouch = true; I.fire = Math.random() < 0.15 && c.blind < 3; return; }
    if (c.throwT >= 0) { c.pitch = damp(c.pitch, this.throwPitch || 0.44, 12, dt); return; }
    if (c.meleeT >= 0) return;
    for (const g of Grenades.list) {
      if (g.kind !== 'frag' || g.stopped && g.fuse > 2) continue;
      const dx = c.x - g.x, dz = c.z - g.z, dd = Math.hypot(dx, dz);
      if (dd < 7.5 && g.fuse > 0.3) {
        const ax = dx / (dd || 1), az = dz / (dd || 1), sn = Math.sin(c.yaw), cs = Math.cos(c.yaw);
        I.mx = ax * cs - az * sn; I.mz = -ax * sn - az * cs; I.sprint = true;
        if (dd < 2.2) I.crouch = true;
        return;
      }
    }
    if (this.nadeCd <= 0 && tgt && this.lastSeenPos && now - this.lastSeenT < 6 && c.reloadT < 0 && c.swapT <= 0) {
      const tx = this.lastSeenPos[0], tz = this.lastSeenPos[1], dd = Math.hypot(tx - c.x, tz - c.z);
      const k = (c.inv.flash > 0 && (c.inv.frag <= 0 || Math.random() < 0.35)) ? 'flash' : (c.inv.frag > 0 ? 'frag' : null);
      if (k && dd > 9 && dd < 30 && World.los([c.x, c.y + 1.5, c.z], [tx, c.y + 1.5, tz])) {
        this.nadeCd = rnd(16, 30);
        c.nade = k; c.yaw = Math.atan2(-(tx - c.x), -(tz - c.z)); this.throwPitch = 0.44;
        c.throwSpeed = Math.sqrt(10.2 * dd) * rnd(0.97, 1.03);
        c.in.throwStart = true; c.in.throwHeld = false;
        return;
      } else this.nadeCd = rnd(3, 6);
    }
    // тяжёлое кровотечение в бою — жгут из укрытия
    if (PARTS.some(k => c.parts[k].hb) && this.state === 'cover' && !c.healing && c.inv.tourniquet > 0 && now - c.lastHitT > 1.2) c.startHeal('tourniquet');

    const hurt = c.parts.thorax.hp < 30 || c.parts.head.hp < 14 || c.totalHP() < 150;
    // ---- выбор состояния ----
    if (engaged) {
      if ((c.suppress > 0.55 || hurt || empty && c.reloadT < 0 && reserve > 0) && this.state !== 'cover') {
        const cp = this.findCover(tgt);
        if (cp) { this.state = 'cover'; this.coverPos = cp; this.coverT = rnd(1.8, 4.2); this.goal = null; this.path = null; }
        else this.state = 'combat';
      } else if (this.state !== 'cover') this.state = 'combat';
    } else if (this.heard && now - this.heard.t < 10) this.state = 'investigate';
    else if (this.state === 'combat' || this.state === 'cover') this.state = 'search';
    else if (this.state === 'search' && now - this.lastSeenT > 12) this.state = 'patrol';
    else if (this.state === 'investigate') this.state = 'patrol';
    if (this.state === 'cover') {
      this.coverT -= dt;
      if (this.coverT <= 0 && !(hurt && c.suppress > 0.3)) this.state = engaged ? 'combat' : 'search';
    }

    switch (this.state) {
      case 'combat': this.doCombat(dt, tgt); break;
      case 'cover': this.doCover(dt, tgt); break;
      case 'search': {
        const lp = this.lastSeenPos;
        if (lp) { this.go(lp[0], lp[1], dt, this.sprintOK && this.d.skill > 0.5 && now - this.lastSeenT > 3, lp[2]); if (this.arrived(lp[0], lp[1], 2.5, lp[2])) { this.lastSeenPos = null; this.state = 'patrol'; } }
        else this.state = 'patrol';
        break;
      }
      case 'investigate': {
        const h = this.heard;
        if (h) { this.go(h.x, h.z, dt, false, h.y); if (this.arrived(h.x, h.z, 3, h.y)) { this.heard = null; this.state = 'patrol'; } }
        else this.state = 'patrol';
        break;
      }
      default: this.doPatrol(dt);
    }
    // обновление отдачи: компенсация
    this.stuckCheck += dt;
    if (this.stuckCheck > 1) {
      const moved = Math.hypot(c.x - this.lastPos[0], c.z - this.lastPos[1]);
      if (this.goal && moved < 0.25 && (I.mx || I.mz)) { this.stuckT++; this.path = null; if (this.stuckT >= 3) { this.goal = null; this.stuckT = 0; this.wait = 0; if (this.state === 'patrol') this.pickWaypoint(); } }
      else this.stuckT = 0;
      this.lastPos = [c.x, c.z]; this.stuckCheck = 0;
    }
  }
  /* --- движение --- */
  arrived(x, z, r, y) { return Math.hypot(this.c.x - x, this.c.z - z) < r && (y === undefined || Math.abs(this.c.y - y) < 1.6); }
  go(x, z, dt, sprint, y) {
    const c = this.c, I = c.in, now = Game.time;
    if (y === undefined) y = c.y;
    this.pathAge += dt;
    const gy = this.goal && this.goal[2] !== undefined ? this.goal[2] : y;
    const moved = !this.goal || Math.hypot(this.goal[0] - x, this.goal[1] - z) > 3.5 || Math.abs(gy - y) > 1.2;
    if ((moved || !this.path || this.pathAge > (this.partial ? 1.5 : 5)) && now >= (this.pathFailT || 0) && (this.pathAge > 0.5 || !this.path) && World.pathSpent < 6) {
      this.goal = [x, z, y]; this.pathAge = 0; this.pi = 0;
      const t0 = World.clock();
      this.path = World.findPath(c.x, c.z, x, z, 0, c.y, y) || null; this.partial = !!(this.path && World.partial);
      World.pathSpent += World.clock() - t0 + 0.2;
      if (!this.path) this.pathFailT = now + 0.7 + Math.random() * 0.7;
    }
    if (!this.path) {
      // пути нет (или очередь на расчёт): при неудаче идём напрямую, иначе ждём
      if (this.pathFailT > now) {
        const dx = x - c.x, dz = z - c.z, d = Math.hypot(dx, dz) || 1;
        if (!(this.target && this.targetVisible)) this.turnTo(Math.atan2(-dx, -dz), 6, dt);
        const R = [Math.cos(c.yaw), -Math.sin(c.yaw)], F = [-Math.sin(c.yaw), -Math.cos(c.yaw)];
        I.mx = clamp(dx / d * R[0] + dz / d * R[1], -1, 1); I.mz = clamp(dx / d * F[0] + dz / d * F[1], -1, 1);
      } else this.faceHeading(dt, 3);
      return;
    }
    while (this.pi < this.path.length - 1 && Math.hypot(c.x - this.path[this.pi][0], c.z - this.path[this.pi][1]) < 0.9 && Math.abs(c.y - this.path[this.pi][2]) < 1.1) this.pi++;
    const wp = this.path[this.pi];
    const dx = wp[0] - c.x, dz = wp[1] - c.z, d = Math.hypot(dx, dz);
    if (d < 0.5 && this.pi >= this.path.length - 1) return;
    const want = Math.atan2(-dx, -dz);
    const engagedLook = this.target && this.targetVisible;
    if (!engagedLook) this.turnTo(want, 6, dt);
    const R = [Math.cos(c.yaw), -Math.sin(c.yaw)], F = [-Math.sin(c.yaw), -Math.cos(c.yaw)];
    const ux = dx / d, uz = dz / d;
    I.mx = clamp(ux * R[0] + uz * R[1], -1, 1); I.mz = clamp(ux * F[0] + uz * F[1], -1, 1);
    I.sprint = !!sprint && !engagedLook;
    c.pitch = damp(c.pitch, 0, 4, dt);
  }
  faceHeading(dt, rate) { this.c.pitch = damp(this.c.pitch, 0, 4, dt); }
  turnTo(yaw, rate, dt) { const c = this.c; c.yaw += wrapAngle(yaw - c.yaw) * Math.min(1, rate * dt); }
  doPatrol(dt) {
    const c = this.c;
    if (this.wait > 0) {
      this.wait -= dt; this.scan += dt;
      this.turnTo(this.patrolYaw + Math.sin(this.scan * 0.8) * 0.9, 2, dt);
      c.pitch = damp(c.pitch, 0, 3, dt);
      return;
    }
    if (!this.goal) this.pickWaypoint();
    if (this.goal) {
      this.go(this.goal[0], this.goal[1], dt, false, this.goal[2]);
      if (this.arrived(this.goal[0], this.goal[1], 2.2, this.goal[2])) { this.goal = null; this.path = null; this.wait = rnd(1.5, 4.5); this.patrolYaw = c.yaw + rnd(-1.5, 1.5); }
    }
  }
  // точка внутри ближайшего/случайного здания (укрытие)
  bldgPoint(near, maxD, tgt) {
    const c = this.c, bs = World.buildings.filter(b => !b.ruin && (b.x1 - b.x0) > 5);
    if (!bs.length) return null;
    let list = bs;
    if (near) { list = bs.filter(b => Math.hypot(b.cx - c.x, b.cz - c.z) < maxD); if (!list.length) return null; }
    for (let k = 0; k < 8; k++) {
      const b = pick(list), H = Math.max(b.h || 3, 3), fl = Math.max(1, Math.round(H / 3));
      const x = rnd(b.x0 + 1, b.x1 - 1), z = rnd(b.z0 + 1, b.z1 - 1), y = Math.min(fl - 1, rndi(0, fl - 1)) * 3;
      const nd = World.surfAt(x, z, y, 1.4);
      if (nd < 0 || !World.reach[nd]) continue;
      const fy = World.sY[nd];
      if (tgt && World.los([x, fy + 1.35, z], tgt.rig.H)) continue;
      return [x, z, fy];
    }
    return null;
  }
  pickWaypoint() {
    const c = this.c;
    if (this.campy === undefined) this.campy = Math.random() < 0.6;
    if (this.campy && Math.random() < 0.55) { const p = this.bldgPoint(false, 0, null); if (p && Math.hypot(p[0] - c.x, p[1] - c.z) > 8) { this.goal = p; this.path = null; return; } }
    for (let k = 0; k < 6; k++) {
      const w = pick(World.waypoints);
      if (Math.hypot(w[0] - c.x, w[1] - c.z) + Math.abs(w[2] - c.y) * 3 > 15) { this.goal = [w[0], w[1], w[2]]; this.path = null; return; }
    }
    this.goal = null;
  }
  findCover(tgt) {
    const c = this.c; if (!tgt) return null;
    const th = tgt.rig.H;
    let best = null, bs = 1e9;
    for (let i = 0; i < 22; i++) {
      const a = Math.random() * Math.PI * 2, r = rnd(3, 13);
      const x = c.x + Math.cos(a) * r, z = c.z + Math.sin(a) * r;
      const nd = World.surfAt(x, z, c.y, 0.6);
      if (nd < 0 || !World.reach[nd]) continue;
      const fy = World.sY[nd];
      if (World.los([x, fy + 1.35, z], th)) continue;
      const s = r + Math.hypot(x - tgt.x, z - tgt.z) < 12 ? 20 : 0;
      const sc = r + s + (World.los([x, fy + 0.9, z], th) ? 4 : 0);
      if (sc < bs) { bs = sc; best = [x, z, fy]; }
    }
    // здания как выгодное укрытие
    for (let k = 0; k < 3; k++) {
      const p = this.bldgPoint(true, 40, tgt); if (!p) break;
      const d = Math.hypot(p[0] - c.x, p[1] - c.z);
      const sc = d * 0.6 - 6 + (Math.hypot(p[0] - tgt.x, p[1] - tgt.z) < 10 ? 20 : 0);
      if (sc < bs) { bs = sc; best = p; }
    }
    return best;
  }
  doCover(dt, tgt) {
    const c = this.c, I = c.in;
    if (this.coverPos) {
      if (!this.arrived(this.coverPos[0], this.coverPos[1], 0.8, this.coverPos[2])) this.go(this.coverPos[0], this.coverPos[1], dt, true, this.coverPos[2]);
      else { I.crouch = true; if (tgt) this.turnTo(Math.atan2(-(tgt.x - c.x), -(tgt.z - c.z)), 3, dt); }
    }
    if (c.reloadT < 0 && c.weapon.mag < c.weapon.def.mag * 0.5 && c.ammoReserve() > 0) I.reload = true;
  }
  doCombat(dt, tgt) {
    const c = this.c, I = c.in, def = c.weapon.def, now = Game.time;
    if (!tgt) return;
    const ch = tgt.rig.C, hd = tgt.rig.H, eye = c.rig.H;
    const dx = tgt.x - c.x, dz = tgt.z - c.z, dist = Math.hypot(dx, dz);
    c.aimDist = Math.max(8, Math.hypot(dx, dz));
    const pref = def.kind === 'pistol' ? 14 : 22 + this.d.skill * 12;
    if (this.targetVisible) {
      // точка прицеливания
      const cart = CART[def.cart], tof = flightTime(cart, dist);
      let ap = ch;
      if (this.d.skill > 0.6 && Math.random() < 0.002 * (1 + this.d.skill * 4)) this.aimHead = !this.aimHead;
      if (this.aimHead && World.los(eye, hd)) ap = hd;
      const lead = this.d.skill * 0.8;
      const tx = ap[0] + tgt.vx * tof * lead, ty = ap[1], tz = ap[2] + tgt.vz * tof * lead;
      // ошибка прицеливания
      this.aimErrT -= dt;
      if (this.aimErrT <= 0) {
        this.aimErrT = rnd(0.25, 0.6);
        const mag = (0.012 + (1 - this.d.skill) * 0.045) * (c.shake * 0.8) * (1 + c.speed * 0.12) * (1 + c.suppress * 1.5) * (1 + Math.min(dist, 150) / 220);
        this.aimErr = [rnd(-1, 1) * mag, rnd(-1, 1) * mag];
      }
      const ddx = tx - eye[0], ddy = ty - eye[1], ddz = tz - eye[2], dd = Math.hypot(ddx, ddz);
      const wantYaw = Math.atan2(-ddx, -ddz) + this.aimErr[0];
      const wantPitch = Math.atan2(ddy, dd) + this.aimErr[1];
      const rate = this.d.aim * (c.stun > 0 ? 0.4 : 1);
      c.yaw += wrapAngle(wantYaw - c.yaw) * Math.min(1, rate * dt);
      c.pitch += (wantPitch - c.pitch) * Math.min(1, rate * dt);
      I.ads = dist > 12;
      // огонь
      const wf = c.rig.wf, dir = V.norm([ddx, ddy, ddz]);
      const ang = Math.acos(clamp(V.dot(wf, dir), -1, 1));
      const ok = ang < 0.035 + 0.9 / Math.max(10, dist) && now - this.acqT > this.d.react * 0.5 && c.lowReady < 0.15 && c.reloadT < 0 && c.swapT <= 0 && dist < 190 * (def.kind === 'pistol' ? 0.3 : 1);
      this.burstT -= dt; this.pauseT -= dt;
      if (ok) {
        if (def.modes.length === 1 || c.weapon.mode === 'semi') {
          this.semiT = (this.semiT || 0) - dt;
          if (this.semiT <= 0) { I.fire = true; this.semiT = rnd(0.16, 0.4) * (1.3 - this.d.skill * 0.5); }
        } else if (this.burstT > 0) I.fire = true;
        else if (this.pauseT <= 0) { this.burstT = rnd(0.18, 0.5) * (0.7 + this.d.skill * 0.6); this.pauseT = rnd(0.35, 1.0) * (1.3 - this.d.skill * 0.6); }
      }
      // манёвр
      this.strafeT -= dt;
      if (this.strafeT <= 0) { this.strafeT = rnd(0.9, 2.6); this.strafe = Math.random() < 0.5 ? -1 : 1; this.crouchT = Math.random() < 0.3 * this.d.skill ? rnd(1, 2.5) : 0; }
      this.crouchT -= dt;
      if (dist > pref * 1.6 && !this.arrived(tgt.x, tgt.z, 6)) {
        // сближение короткими рывками, не бегом под огнём
        this.go(tgt.x, tgt.z, dt, false, tgt.y);
        I.ads = false;
      } else {
        I.mx = this.strafe * (0.6 + 0.4 * this.d.skill) * (c.legFactor() > 0.6 ? 1 : 0.4);
        if (dist < pref * 0.5) I.mz = -0.8;
        I.crouch = this.crouchT > 0;
        // не упираться в стены при стрейфе
        if (World.blockedAt(c.x + Math.cos(c.yaw) * I.mx * 0.7, c.y, c.z - Math.sin(c.yaw) * I.mx * 0.7, 0.4, 1.4)) this.strafe = -this.strafe;
      }
    } else {
      // цель потеряна — идём к последней точке контакта, держа оружие наготове
      const lp = this.lastSeenPos;
      if (lp) { this.go(lp[0], lp[1], dt, false, lp[2]); const d2 = Math.hypot(lp[0] - c.x, lp[1] - c.z); if (d2 < 3 && Math.abs((lp[2] === undefined ? c.y : lp[2]) - c.y) < 1.6) { this.lastSeenPos = null; } }
      I.ads = false;
    }
  }
}

function spawnBots(n, diffI, armor) {
  const d = DIFFS[clamp(diffI, 0, 3)];
  const used = [];
  const pl = Game.player;
  const pool = World.botSpawns.filter(p => Math.hypot(p[0] - pl.x, p[1] - pl.z) > (World.spawnMin || 55));
  for (let i = 0; i < n; i++) {
    let p = null;
    for (let k = 0; k < 40; k++) {
      const q = pick(pool);
      if (used.every(u => Math.hypot(u[0] - q[0], u[1] - q[1]) > 18)) { p = q; break; }
    }
    if (!p) p = pick(pool);
    used.push(p);
    const b = new Combatant({
      name: CALLSIGNS[i % CALLSIGNS.length], team: Game.mode === 'ffa' ? 10 + i : 1, x: p[0], z: p[1], y: p[2], yaw: rnd(0, Math.PI * 2),
      primary: Math.random() < 0.5 ? 'm4' : 'akm', armor, mags: 3 + rndi(0, 2), inv: { bandage: 2, tourniquet: 1, splint: 1, pills: 1, medPool: 140, frag: Math.random() < 0.6 ? 1 : 0, flash: Math.random() < 0.4 ? 1 : 0 },
    });
    b.brain = new Brain(b, { ...d, skill: clamp(d.skill + rnd(-0.08, 0.08), 0.2, 1), react: d.react * rnd(0.85, 1.2) });
    b.isBot = true;
    Game.combatants.push(b);
  }
}

Bus.on('shot', e => {
  const s = e.c;
  for (const b of Game.combatants) {
    if (!b.brain || !b.alive || b === s || b.team === s.team) continue;
    const d = Math.hypot(b.x - s.x, b.z - s.z), range = 330 * e.def.loud;
    if (d < range) b.brain.hear(s.x, s.z, d, 'shot', s.y);
  }
});
Bus.on('step', e => {
  const s = e.c;
  for (const b of Game.combatants) {
    if (!b.brain || !b.alive || b === s || b.team === s.team) continue;
    const d = Math.hypot(b.x - s.x, b.z - s.z);
    if (d < 24 * e.loud && d > 0.5) b.brain.hear(s.x, s.z, d, 'step', s.y);
  }
});

if (typeof module !== 'undefined') module.exports = { Brain, spawnBots, DIFFS };

/* --- 45_game.js --- */
/* ===== Игровой цикл симуляции ===== */
Game.reset = function (o) {
  o = o || {};
  this.combatants = []; Ballistics.list = []; Ballistics.acc = 0; Grenades.reset();
  this.time = 0; this.over = false; this.result = null;
  this.mode = o.mode || 'team'; this.difficulty = o.difficulty === undefined ? 1 : o.difficulty;
  this.botCount = o.bots || 8; this.armor = o.armor === undefined ? 3 : o.armor;
  for (const p of World.pickups) p.taken = false;
  const sp = World.spawnPlayer;
  const pl = new Combatant({
    name: 'Вы', team: 0, isPlayer: true, x: sp[0], z: sp[1], yaw: sp[3] || 0, primary: o.primary || 'm4', armor: this.armor, mags: 5,
    inv: { bandage: 4, tourniquet: 2, splint: 2, pills: 2, medPool: 260, frag: 2, flash: 1 },
  });
  pl.weapons[1].reserve = [17, 17, 17];
  this.player = pl;
  this.combatants.push(pl);
  spawnBots(this.botCount, this.difficulty, this.armor);
};

// чистый сброс мира для сервера/клиента мультиплеера (без игрока и ботов)
Game.resetNet = function () {
  this.combatants = []; Ballistics.list = []; Ballistics.acc = 0; Grenades.reset();
  this.time = 0; this.over = false; this.result = null; this.net = true;
  for (const p of World.pickups) { p.taken = false; p.respT = 0; }
};

Game.alive = function () { return this.combatants.filter(c => c.alive && !c.isPlayer).length; };

Game.update = function (dt) {
  dt = Math.min(dt, 0.05);
  this.time += dt;
  World.pathSpent = 0;
  for (const c of this.combatants) if (c.brain) c.brain.think(dt);
  for (const c of this.combatants) c.update(dt);
  // мягкое расталкивание бойцов
  const L = this.combatants;
  for (let i = 0; i < L.length; i++) for (let j = i + 1; j < L.length; j++) {
    const a = L[i], b = L[j];
    if (!a.alive || !b.alive) continue;
    const dx = b.x - a.x, dz = b.z - a.z, d = Math.hypot(dx, dz);
    if (d < 0.6 && d > 0.001) {
      const push = (0.6 - d) * 0.5, ux = dx / d, uz = dz / d;
      if (!World.blockedAt(a.x - ux * push, a.y, a.z - uz * push, 0.35, 1.5)) { a.x -= ux * push; a.z -= uz * push; }
      if (!World.blockedAt(b.x + ux * push, b.y, b.z + uz * push, 0.35, 1.5)) { b.x += ux * push; b.z += uz * push; }
    }
  }
  Ballistics.update(dt);
  Grenades.update(dt);
  if (this.lagComp) for (const c of L) { if (!c.rig) continue; c.hist.push({ t: this.time, x: c.x, y: c.y, z: c.z, caps: c.rig.caps }); while (c.hist.length > 2 && c.hist[0].t < this.time - 0.6) c.hist.shift(); }
  if (!this.over && !this.net) {
    if (!this.player.alive) { this.over = true; this.result = 'dead'; Bus.emit('gameover', 'dead'); }
    else if (this.alive() === 0) { this.over = true; this.result = 'win'; Bus.emit('gameover', 'win'); }
  }
};

// подбор предметов
Game.nearestPickup = function (c, maxD) {
  let best = null, bd = maxD || 2.2;
  for (const p of World.pickups) {
    if (p.taken || Math.abs((p.y || 0) - c.y) > 1.8) continue;
    const d = Math.hypot(p.x - c.x, p.z - c.z);
    if (d < bd) { bd = d; best = p; }
  }
  return best;
};
Game.takePickup = function (c, p) {
  p.taken = true;
  if (p.type === 'med') {
    const got = [];
    const add = (k, n) => { c.inv[k] = (c.inv[k] || 0) + n; got.push(ITEMS[k].ru + ' ×' + n); };
    add('bandage', rndi(1, 2));
    if (Math.random() < 0.6) add('tourniquet', 1);
    if (Math.random() < 0.5) add('splint', 1);
    if (Math.random() < 0.6) add('pills', 1);
    if (Math.random() < 0.7) { const m = rndi(40, 90); c.inv.medPool += m; got.push('Аптечка +' + m); }
    return got.join(', ');
  }
  const w = c.weapons[0], g = c.weapons[1];
  for (let i = 0; i < 2; i++) w.reserve.push(w.def.mag);
  g.reserve.push(g.def.mag);
  return 'Магазины: ' + w.def.name + ' ×2, ' + g.def.name + ' ×1';
};

if (typeof module !== 'undefined') module.exports = {};

/* --- 46_net_common.js --- */
/* ===== Сеть: общие функции упаковки состояния (клиент и сервер) ===== */
const NET = {
  VER: 1,
  F: ['x', 'y', 'z', 'yaw', 'pitch', 'vx', 'vz', 'speed', 'lmx', 'lmz', 'gait', 'crouch', 'leanA', 'ads', 'lowReady', 'punchP', 'punchY', 'swayP', 'swayY', 'reloadT', 'reloadDur', 'swapT', 'throwT', 'throwRelT', 'meleeT', 'idleLow', 'ht'],
  PREC: [100, 100, 100, 1000, 1000, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 1000, 1000, 1000, 1000, 100, 100, 100, 100, 100, 100, 100, 100],
  HT: ['', 'bandage', 'tourniquet', 'splint', 'pills', 'medkit'],
  pack(c) {
    const F = this.F, P = this.PREC, a = new Array(F.length + 1);
    let fl = 0;
    if (c.grounded) fl |= 1; if (c.sprinting) fl |= 2; if (c.throwRel) fl |= 4; if (c.meleeKind === 'stab') fl |= 8; if (c.nade === 'flash') fl |= 16;
    if (c.alive) fl |= 32; if (c.cur) fl |= 64; if (c.swapTo) fl |= 128; if (c.reloadKind === 'empty') fl |= 262144;
    const PARTS_ = PARTS; let bm = 0; for (let i = 0; i < 7; i++) if (c.parts[PARTS_[i]].black) bm |= 1 << i;
    fl |= bm << 8; fl |= (c.healing ? Math.max(1, this.HT.indexOf(c.healing.type)) : 0) << 15;
    a[0] = fl;
    for (let i = 0; i < F.length; i++) {
      let v = F[i] === 'ht' ? (c.healing ? c.healing.t : 0) : c[F[i]];
      if (v === undefined || v !== v) v = 0;
      a[i + 1] = Math.round(v * P[i]) / P[i];
    }
    return a;
  },
  apply(c, a, srv) {
    const F = this.F, fl = a[0];
    for (let i = 0; i < F.length; i++) { if (F[i] !== 'ht') c[F[i]] = a[i + 1]; }
    c.grounded = !!(fl & 1); c.sprinting = !!(fl & 2); c.throwRel = !!(fl & 4); c.meleeKind = (fl & 8) ? 'stab' : 'slash'; c.nade = (fl & 16) ? 'flash' : 'frag';
    c.cur = (fl & 64) ? 1 : 0; c.swapTo = (fl & 128) ? 1 : 0; c.reloadKind = (fl & 262144) ? 'empty' : 'tac';
    if (srv) return;
    const bm = (fl >> 8) & 127; for (let i = 0; i < 7; i++) c.parts[PARTS[i]].black = !!(bm & (1 << i));
    const hi = (fl >> 15) & 7;
    if (hi) { const type = this.HT[hi]; c.healing = { type, part: 'any', t: a[F.length], dur: ITEMS[type].t }; } else c.healing = null;
  },
  alive(a) { return !!(a[0] & 32); },
  // жизненные показатели игрока (только владельцу)
  vitals(c) {
    const v = { p: [], a: [], pain: +c.pain.toFixed(1), pk: +c.painkiller.toFixed(1), st: +c.stun.toFixed(2), bl: +c.blind.toFixed(2), bm: +c.blindMax.toFixed(2), df: +c.deaf.toFixed(2), bld: +(c.bleeding || 0).toFixed(2), inv: c.inv };
    for (const k of PARTS) { const q = c.parts[k]; v.p.push([+q.hp.toFixed(1), (q.black ? 1 : 0) | (q.lb ? 2 : 0) | (q.hb ? 4 : 0) | (q.fx ? 8 : 0)]); }
    for (const k in c.armor) v.a.push([k, +c.armor[k].dur.toFixed(1)]);
    return v;
  },
  applyVitals(c, v) {
    for (let i = 0; i < 7; i++) { const q = c.parts[PARTS[i]], x = v.p[i]; q.hp = x[0]; q.black = !!(x[1] & 1); q.lb = !!(x[1] & 2); q.hb = !!(x[1] & 4); q.fx = !!(x[1] & 8); }
    for (const [k, d] of v.a) if (c.armor[k]) c.armor[k].dur = d;
    c.pain = v.pain; c.painkiller = v.pk; c.stun = Math.max(c.stun, v.st); if (v.bl > c.blind) { c.blind = v.bl; c.blindMax = v.bm; } if (v.df > c.deaf) c.deaf = v.df; c.bleeding = v.bld;
    Object.assign(c.inv, v.inv);
  },
  info(c) { return { id: c.id, name: c.name, team: c.team, bot: !!c.isBot, pri: c.weapons[0].def.id, human: !!c.isHuman, pid: c.pid }; },
};
if (typeof module !== 'undefined') module.exports = { NET };

/* --- match.js --- */
/* ===== Сервер мультиплеера: слоты игроков, режимы, спавн, снапшоты ===== */
const TEAM_NAMES = ['СИНИЕ', 'КРАСНЫЕ'];
const MODES = {
  tdm: { id: 'tdm', ru: 'Командный бой', team: true, limit: 40, time: 720, resp: 6 },
  ffa: { id: 'ffa', ru: 'Каждый за себя', team: false, limit: 25, time: 600, resp: 4 },
  elim: { id: 'elim', ru: 'Элиминация', team: true, limit: 4, time: 900, resp: -1 },
  koth: { id: 'koth', ru: 'Удержание точки', team: true, limit: 150, time: 720, resp: 6 },
  coop: { id: 'coop', ru: 'Зачистка (кооп)', team: true, coop: true, limit: 10, time: 1500, resp: -1 },
};
const SV = {
  cfg: { target: 10, diff: 1, armor: 3, rotation: ['tdm', 'koth', 'elim', 'ffa', 'coop'], snapHz: 20, maxPlayers: 12 },
  slots: [], nextPid: 1, botN: 0, rot: 0, M: null, out: null, tAcc: 0, sbT: 0, vitT: 0, snapT: 0, idle: true, log: () => { },
  /* ---------- вспомогательное ---------- */
  humans() { return this.slots.filter(s => s.human); },
  send(slot, o) { if (slot.human && this.out) this.out(slot, o); },
  bcast(o, except) { const s = JSON.stringify(o); for (const sl of this.slots) if (sl.human && sl !== except && this.outRaw) this.outRaw(sl, s); },
  /* ---------- вход/выход ---------- */
  join(sendObj, sendRaw, name, pri) {
    const hs = this.humans();
    if (hs.length >= this.cfg.maxPlayers) return null;
    const sl = { pid: this.nextPid++, human: true, name: String(name || 'Игрок').slice(0, 16), team: 0, c: null, kills: 0, deaths: 0, score: 0, pri: pri === 'akm' ? 'akm' : 'm4', respT: 0, rtt: 80, ping: 0, lastSt: 0, lastShot: 0, joinT: this.now() };
    this.slots.push(sl);
    sl.team = this.assignTeam(sl);
    if (this.idle) { this.idle = false; this.startMatch(this.cfg.rotation[this.rot % this.cfg.rotation.length]); }
    else this.autoSpawn(sl, true);
    return sl;
  },
  leave(sl) {
    if (sl.c) { sl.c.alive = false; this.removeEntity(sl.c); }
    this.slots = this.slots.filter(s => s !== sl);
    this.bcast({ t: 'chat', n: '', m: sl.name + ' вышел' });
    if (!this.humans().length) this.goIdle();
  },
  goIdle() {
    for (const s of this.slots.slice()) if (s.c) this.removeEntity(s.c);
    this.slots = []; Game.resetNet(); Grenades.reset(); this.idle = true; this.M = null;
  },
  now() { return Game.time; },
  assignTeam(sl) {
    const M = this.M, mode = M ? M.mode : MODES.tdm;
    if (!mode.team) return 100 + sl.pid;
    if (mode.coop) return 0;
    const cnt = [0, 0]; for (const s of this.slots) if (s !== sl && s.human && s.team < 2) cnt[s.team]++;
    if (cnt[0] !== cnt[1]) return cnt[0] < cnt[1] ? 0 : 1;
    const sc = M ? M.score : [0, 0]; return sc[0] <= sc[1] ? 0 : 1;
  },
  /* ---------- спавн ---------- */
  pickSpawn(team, modeTeam) {
    const pts = World.botSpawns.concat([World.spawnPlayer]);
    const foes = Game.combatants.filter(c => c.alive && c.team !== team), mates = Game.combatants.filter(c => c.alive && c.team === team);
    let best = [], bs = -1e9;
    for (const p of pts) {
      let md = 1e9; for (const f of foes) md = Math.min(md, Math.hypot(f.x - p[0], f.z - p[1]));
      let near = 0; for (const m of mates) if (Math.hypot(m.x - p[0], m.z - p[1]) < 6) near++;
      let sc = Math.min(md, 90) - near * 12;
      if (modeTeam && team < 2) sc += (team === 0 ? (p[1] > 30 ? 55 : 0) : (p[1] < -30 ? 55 : 0));
      if (md < 18) sc -= 200;
      best.push([sc, p]);
    }
    best.sort((a, b) => b[0] - a[0]);
    const top = best.slice(0, 4); return pick(top)[1];
  },
  makeEntity(sl) {
    const mode = this.M.mode, sp = this.pickSpawn(sl.team, mode.team && !mode.coop);
    const yaw = Math.atan2(sp[0], sp[1]);
    const inv = sl.human ? { bandage: 3, tourniquet: 2, splint: 1, pills: 1, medPool: 220, frag: 2, flash: 1 } : { bandage: 2, tourniquet: 1, splint: 1, pills: 1, medPool: 140, frag: Math.random() < 0.6 ? 1 : 0, flash: Math.random() < 0.4 ? 1 : 0 };
    const c = new Combatant({ name: sl.name, team: sl.team, x: sp[0], z: sp[1], y: sp[2], yaw, primary: sl.human ? sl.pri : (Math.random() < 0.5 ? 'm4' : 'akm'), armor: this.cfg.armor, mags: sl.human ? 5 : 3 + rndi(0, 2), inv });
    c.slot = sl; sl.c = c;
    if (sl.human) { c.isHuman = true; c.netMode = 'human'; c.pid = sl.pid; c.protT = 2.5; c.weapons[1].reserve = [17, 17, 17]; c.protT = 2.5; }
    else {
      c.isBot = true; const d = DIFFS[clamp(this.cfg.diff + (mode.coop ? Math.min(2, Math.floor(this.M.wave / 4)) : 0), 0, 3)];
      c.brain = new Brain(c, { ...d, skill: clamp(d.skill + rnd(-0.08, 0.08), 0.2, 1), react: d.react * rnd(0.85, 1.2) }); c.protT = 1.5;
    }
    c.hist = []; Game.combatants.push(c);
    this.bcast({ t: 'ent', add: [Object.assign(NET.info(c), { st: NET.pack(c) })] }, sl.human ? sl : undefined);
    return c;
  },
  removeEntity(c) {
    const i = Game.combatants.indexOf(c); if (i >= 0) Game.combatants.splice(i, 1);
    if (c.slot && c.slot.c === c) c.slot.c = null;
    this.bcast({ t: 'ent', del: [c.id] });
  },
  autoSpawn(sl, first) {
    if (!this.M) return;
    const M = this.M;
    if (sl.c && sl.c.alive) return;
    if (sl.c) { const old = sl.c; sl.c = null; M.corpses.push({ c: old, t: Game.time + 12 }); }
    if (M.mode.id === 'elim' && M.phase === 'live' && !first) { sl.respT = -1; return; }
    if (M.mode.coop && M.phase === 'live' && !first) { sl.respT = -1; return; }
    const c = this.makeEntity(sl);
    sl.respT = 0;
    if (sl.human) this.send(sl, { t: 'spawn', e: c.id, x: c.x, y: c.y, z: c.z, yaw: c.yaw, pri: sl.pri, team: sl.team, inv: c.inv });
  },
  /* ---------- матч ---------- */
  startMatch(modeId) {
    const mode = MODES[modeId] || MODES.tdm;
    for (const c of Game.combatants.slice()) this.removeEntity(c);
    Game.resetNet(); Game.lagComp = true; Game.noFF = true;
    this.M = { mode, phase: 'live', t: 0, score: [0, 0], wave: 0, corpses: [], round: 0, wins: [0, 0], phT: 0, msg: '', koth: null, winner: null };
    for (const s of this.slots) { s.kills = s.deaths = s.score = 0; s.c = null; if (s.human) s.team = this.assignTeam(s); }
    this.slots = this.slots.filter(s => s.human);
    // распределение команд игроков по очереди
    if (mode.team && !mode.coop) { let k = 0; for (const s of this.humans()) s.team = (k++) % 2; }
    if (mode.coop) for (const s of this.humans()) s.team = 0;
    if (!mode.team) for (const s of this.humans()) s.team = 100 + s.pid;
    this.bcast({ t: 'match', id: mode.id, ru: mode.ru, team: mode.team, coop: !!mode.coop });
    if (mode.id === 'elim') { this.startRound(); }
    else if (mode.id === 'coop') { this.startWave(); }
    else {
      for (const s of this.humans()) { this.send(s, { t: 'team', team: s.team }); this.autoSpawn(s, true); }
      if (mode.id === 'koth') this.kothInit();
    }
    this.fillBots();
    this.log('матч', mode.id);
  },
  fillBots() {
    const M = this.M; if (!M) return;
    const mode = M.mode;
    if (mode.coop) return;
    if (mode.id === 'elim' && M.phase !== 'freeze') return;
    const hs = this.humans(), want = Math.max(0, this.cfg.target - hs.length);
    const bots = this.slots.filter(s => !s.human);
    // для командных режимов — по командам
    if (mode.team) {
      const cnt = [0, 0]; for (const s of hs) cnt[s.team]++;
      const per = [Math.ceil((this.cfg.target) / 2), Math.floor(this.cfg.target / 2)];
      for (const t of [0, 1]) {
        const need = Math.max(0, per[t] - cnt[t]), have = bots.filter(b => b.team === t);
        for (let i = have.length; i < need; i++) this.addBot(t);
        for (let i = need; i < have.length; i++) this.dropBot(have[i]);
      }
    } else {
      for (let i = bots.length; i < want; i++) this.addBot(10 + (this.botN % 90));
      for (let i = want; i < bots.length; i++) this.dropBot(bots[i]);
    }
  },
  addBot(team) {
    const sl = { pid: -(++this.botN), human: false, name: CALLSIGNS[this.botN % CALLSIGNS.length], team: team >= 10 ? 10 + this.botN : team, c: null, kills: 0, deaths: 0, score: 0, respT: 0, bot: true };
    this.slots.push(sl); this.autoSpawn(sl, true); return sl;
  },
  dropBot(sl) { if (sl.c) this.removeEntity(sl.c); this.slots = this.slots.filter(s => s !== sl); },
  /* ---------- раунды (элиминация) ---------- */
  startRound() {
    const M = this.M; M.round++; M.phase = 'freeze'; M.phT = 7; M.msg = 'Раунд ' + M.round;
    for (const c of Game.combatants.slice()) this.removeEntity(c);
    for (const s of this.slots) s.c = null;
    this.slots = this.slots.filter(s => s.human);
    this.fillBots();
    for (const s of this.humans()) { this.autoSpawn(s, true); }
    this.bcast({ t: 'phase', ph: 'freeze', ms: M.msg, tl: M.phT });
  },
  // координаты точки для удержания
  kothInit() {
    const M = this.M, W = World.waypoints, targets = World.koth;
    M.koth = { spots: targets.map(t => { let b = W[0], bd = 1e9; for (const w of W) { const d = Math.hypot(w[0] - t[0], w[1] - t[1]); if (d < bd) { bd = d; b = w; } } return [b[0], b[1]]; }), i: 0, owner: -1, prog: 0, mv: 100, r: 10 };
  },
  /* ---------- волны (кооп) ---------- */
  startWave() {
    const M = this.M; M.wave++; M.phase = 'live'; M.phT = 0; M.msg = 'Волна ' + M.wave;
    for (const s of this.humans()) if (!s.c || !s.c.alive) { s.team = 0; this.autoSpawn(s, true); }
    const n = Math.min(4 + M.wave * 2, 16);
    for (const s of this.slots.filter(x => !x.human)) this.dropBot(s);
    for (let i = 0; i < n; i++) this.addBot(1);
    this.bcast({ t: 'phase', ph: 'live', ms: M.msg, tl: 0 });
  },
  endMatch(winner, reason) {
    const M = this.M; if (!M || M.phase === 'over') return;
    M.phase = 'over'; M.phT = 14; M.winner = winner; M.msg = reason || '';
    this.bcast({ t: 'phase', ph: 'over', ms: reason || '', tl: 14, w: winner });
    this.sendBoard(true);
  },
  /* ---------- события боя ---------- */
  onDeath(e) {
    const v = e.victim, sl = v.slot, a = e.attacker, M = this.M; if (!M || !sl) return;
    sl.deaths++;
    const as = a && a.slot;
    const mode = M.mode;
    if (as && as !== sl) {
      as.kills++; as.score += e.part === 'head' ? 150 : 100;
      if (mode.id === 'tdm' && as.team < 2) M.score[as.team]++;
      if (mode.id === 'ffa') M.score[0] = Math.max(M.score[0], as.kills);
      if (mode.coop) M.score[0]++;
    } else if (as === sl && mode.id === 'tdm' && sl.team < 2) M.score[sl.team ^ 1]++;
    // рэгдолл-данные
    const imp = (v.hitLog || []).filter(h => Game.time - h.t < 0.4).map(h => [h.part, +h.dir[0].toFixed(2), +h.dir[1].toFixed(2), +h.dir[2].toFixed(2), +h.dv.toFixed(1)]);
    const bl = v.blast ? v.blast.map(q => +q.toFixed(1)) : null;
    this.bcast({ t: 'death', v: v.id, a: a ? a.id : 0, part: e.part, dist: Math.round(e.dist || 0), cause: e.cause || '', imp, bl });
    if (sl.human) this.send(sl, { t: 'died', by: a ? a.name : '', part: e.part, resp: mode.resp });
    // возрождение
    if (mode.resp > 0 && M.phase === 'live') sl.respT = mode.resp; else sl.respT = -1;
    if (!sl.human) { if (mode.resp > 0 || mode.id === 'elim') {} }
  },
  tickMatch(dt) {
    const M = this.M; if (!M) return;
    M.t += dt; const mode = M.mode;
    // трупы
    for (let i = M.corpses.length - 1; i >= 0; i--) if (Game.time > M.corpses[i].t) { this.removeEntity(M.corpses[i].c); M.corpses.splice(i, 1); }
    // возрождение
    for (const s of this.slots) {
      if (s.respT > 0 && (!s.c || !s.c.alive)) { s.respT -= dt; if (s.respT <= 0) { s.respT = 0; if (s.human || this.botsWanted(s)) this.autoSpawn(s, false); else { if (s.c) this.removeEntity(s.c); this.slots = this.slots.filter(x => x !== s); } } }
    }
    if (M.phase === 'over') { M.phT -= dt; if (M.phT <= 0) { this.rot++; this.startMatch(this.cfg.rotation[this.rot % this.cfg.rotation.length]); } return; }
    // таймер матча
    if (M.t > mode.time && mode.id !== 'elim' && !mode.coop) { this.finishByScore(); return; }
    if (mode.id === 'tdm' || mode.id === 'koth') {
      const lim = mode.limit; if (M.score[0] >= lim || M.score[1] >= lim) this.finishByScore();
    }
    if (mode.id === 'ffa') {
      if (M.score[0] >= mode.limit) { const top = this.slots.slice().sort((a, b) => b.kills - a.kills)[0]; this.endMatch(top ? top.name : '', top ? 'Победитель: ' + top.name : ''); }
    }
    if (mode.id === 'koth') this.tickKoth(dt);
    if (mode.id === 'elim') this.tickElim(dt);
    if (mode.coop) this.tickCoop(dt);
  },
  botsWanted(s) {
    const M = this.M; if (!M) return false;
    if (M.mode.coop) return false;
    const hs = this.humans();
    if (M.mode.team) { const per = s.team === 0 ? Math.ceil(this.cfg.target / 2) : Math.floor(this.cfg.target / 2); const cnt = hs.filter(h => h.team === s.team).length; const have = this.slots.filter(x => !x.human && x.team === s.team).length; return have <= per - cnt; }
    return this.slots.filter(x => !x.human).length <= this.cfg.target - hs.length;
  },
  finishByScore() {
    const M = this.M, mode = M.mode;
    if (mode.team) { const w = M.score[0] === M.score[1] ? -1 : (M.score[0] > M.score[1] ? 0 : 1); this.endMatch(w, w < 0 ? 'Ничья' : 'Победа: ' + TEAM_NAMES[w]); }
    else { const top = this.slots.slice().sort((a, b) => b.kills - a.kills)[0]; this.endMatch(top ? top.name : '', top ? 'Победитель: ' + top.name : ''); }
  },
  tickKoth(dt) {
    const M = this.M, K = M.koth; if (!K) return;
    K.mv -= dt; if (K.mv <= 0) { K.mv = 100; K.i = (K.i + 1) % K.spots.length; K.owner = -1; K.prog = 0; }
    const sp = K.spots[K.i], cnt = [0, 0];
    for (const c of Game.combatants) if (c.alive && c.team < 2 && Math.hypot(c.x - sp[0], c.z - sp[1]) < K.r) cnt[c.team]++;
    if (cnt[0] && !cnt[1]) { if (K.owner !== 0) { K.prog += dt / 4; if (K.prog >= 1) { K.owner = 0; K.prog = 1; } } else K.prog = 1; K.cap = 0; }
    else if (cnt[1] && !cnt[0]) { if (K.owner !== 1) { K.prog += dt / 4; if (K.prog >= 1) { K.owner = 1; K.prog = 1; } } else K.prog = 1; K.cap = 1; }
    else if (cnt[0] && cnt[1]) K.cap = -2;
    else { K.cap = -1; }
    if (K.owner >= 0 && K.owner < 2 && (K.cap === K.owner || K.cap === -1 || K.cap === undefined)) { K.acc = (K.acc || 0) + dt; if (K.acc >= 1) { K.acc -= 1; M.score[K.owner]++; } }
    // смена владельца: захват противником сбрасывает прогресс
    if (K.cap >= 0 && K.cap !== K.owner && K.owner >= 0) { K.prog -= dt / 3; if (K.prog <= 0) { K.owner = -1; K.prog = 0; } }
  },
  tickElim(dt) {
    const M = this.M;
    if (M.phase === 'freeze') { M.phT -= dt; if (M.phT <= 0) { M.phase = 'live'; M.phT = 150; M.msg = ''; this.bcast({ t: 'phase', ph: 'live', ms: '', tl: 150 }); } return; }
    if (M.phase === 'between') { M.phT -= dt; if (M.phT <= 0) this.startRound(); return; }
    if (M.phase !== 'live') return;
    M.phT -= dt;
    const al = [0, 0]; for (const c of Game.combatants) if (c.alive && c.team < 2) al[c.team]++;
    let w = null;
    if (al[0] === 0 && al[1] === 0) w = -1; else if (al[0] === 0) w = 1; else if (al[1] === 0) w = 0;
    else if (M.phT <= 0) w = al[0] === al[1] ? -1 : (al[0] > al[1] ? 0 : 1);
    if (w !== null) {
      if (w >= 0) M.wins[w]++; M.score = M.wins.slice();
      if (M.wins[0] >= M.mode.limit || M.wins[1] >= M.mode.limit || M.round >= 7) { const f = M.wins[0] === M.wins[1] ? -1 : (M.wins[0] > M.wins[1] ? 0 : 1); this.endMatch(f, f < 0 ? 'Ничья' : 'Победа: ' + TEAM_NAMES[f]); }
      else { M.phase = 'between'; M.phT = 7; this.bcast({ t: 'phase', ph: 'between', ms: w < 0 ? 'Раунд: ничья' : 'Раунд за ' + TEAM_NAMES[w], tl: 7 }); }
    }
  },
  tickCoop(dt) {
    const M = this.M;
    if (M.phase === 'between') { M.phT -= dt; if (M.phT <= 0) this.startWave(); return; }
    if (M.phase !== 'live') return;
    const bots = Game.combatants.filter(c => c.alive && c.isBot).length, hum = Game.combatants.filter(c => c.alive && c.isHuman).length;
    if (!hum && this.humans().length) { this.endMatch(1, 'Отряд погиб. Волна ' + M.wave); return; }
    if (bots === 0) {
      if (M.wave >= M.mode.limit) { this.endMatch(0, 'Все волны отбиты!'); return; }
      M.phase = 'between'; M.phT = 12; M.msg = 'Волна ' + M.wave + ' отбита';
      for (const s of this.humans()) if (s.c && s.c.alive) { const c = s.c; c.inv.bandage += 1; c.inv.medPool = Math.min(300, c.inv.medPool + 60); this.send(s, { t: 'loot', ammo: 2, inv: c.inv }); }
      this.bcast({ t: 'phase', ph: 'between', ms: M.msg, tl: 12 });
    }
  },
  /* ---------- сообщения ---------- */
  msg(sl, m) {
    const c = sl.c; sl.lastMsg = Game.time;
    switch (m.t) {
      case 'st': {
        if (!c || !c.alive || !Array.isArray(m.a)) return;
        const frozen = this.M && this.M.phase === 'freeze';
        const old = [c.x, c.z], dt = Math.max(0.02, Game.time - sl.lastSt); sl.lastSt = Game.time;
        const a = m.a; if (a.length !== NET.F.length + 1) return;
        const nx = a[1], nz = a[3];
        if (!(isFinite(nx) && isFinite(nz))) return;
        const hd = Math.hypot(nx - old[0], nz - old[1]);
        if (hd > 10 * dt + 2.5 && !this.cfg.dev) { sl.viol = (sl.viol || 0) + 1; if (sl.viol > 2) { this.send(sl, { t: 'tp', x: old[0], y: c.y, z: old[1] }); sl.viol = 0; } return; }
        sl.viol = 0;
        NET.apply(c, a, true);
        if (frozen) { c.x = old[0]; c.z = old[1]; }
        break;
      }
      case 'shot': {
        if (!c || !c.alive || !m.p || !m.d) return;
        const wi = m.wi ? 1 : 0, w = c.weapons[wi], def = w.def, cart = CART[def.cart];
        const rtt = clamp(m.rtt || sl.rtt, 0, 600);
        if (Game.time - sl.lastShot < 60 / def.rpm * 0.6) return; sl.lastShot = Game.time;
        if (this.M && this.M.phase === 'freeze') return;
        let d = V.norm([+m.d[0], +m.d[1], +m.d[2]]), p = [+m.p[0], +m.p[1], +m.p[2]];
        if (![...d, ...p].every(isFinite)) return;
        const rg = c.rig; if (rg && V.dist(p, rg.W0) > 1.8) p = V.mad(rg.W0, V.norm(V.sub(p, rg.W0)), 1.0);
        c.protT = 0;
        const lag = clamp((m.lag || 0.1) + 0.0, 0, Math.min(0.3, rtt / 2000 + 0.16));
        Ballistics.spawn(c, cart, p, d, !!m.tr, { lag });
        c.stats.shots++; c.cur = wi;
        Bus.emit('shot', { c, pos: p, dir: d, def, cart, tr: !!m.tr });
        break;
      }
      case 'sfx': {
        if (!c || !SFX_OK[m.k]) return;
        this.bcast({ t: 'sfx', k: m.k, e: c.id }, sl);
        if (m.k === 'dry' || m.k === 'reload') c.reloadT = m.k === 'reload' ? 0 : c.reloadT;
        break;
      }
      case 'heal': if (c && c.alive && ITEMS[m.type]) { c.healing = null; c.startHeal(m.type, PARTS.includes(m.part) ? m.part : undefined); } break;
      case 'throw': {
        if (!c || !c.alive || !GREN[m.k] || !(c.inv[m.k] > 0) || !m.pos || !m.vel) return;
        const p = m.pos.map(Number), v = m.vel.map(Number); if (![...p, ...v].every(isFinite)) return;
        if (V.len(v) > 24 || (c.rig && V.dist(p, c.rig.H) > 3)) return;
        c.inv[m.k]--; c.protT = 0;
        Grenades.spawn(c, m.k, p, v, clamp(+m.fuse || 2, 0.03, 4));
        break;
      }
      case 'melee': if (c && c.alive && c.mT < 0) { c.mT = 0; c.mKind = m.kind === 'stab' ? 'stab' : 'slash'; c.protT = 0; } break;
      case 'pk': {
        const p = World.pickups[m.i | 0]; if (!c || !c.alive || !p || p.taken || Math.hypot(p.x - c.x, p.z - c.z) > 3.2 || Math.abs((p.y || 0) - c.y) > 1.8) return;
        const got = this.rollLoot(c, p); p.taken = true; p.respT = 70;
        this.bcast({ t: 'pk', i: m.i | 0, taken: true });
        this.send(sl, { t: 'loot', ammo: p.type === 'med' ? 0 : 1, inv: c.inv, txt: got });
        break;
      }
      case 'chat': { const txt = String(m.m || '').slice(0, 120).replace(/[<>]/g, ''); if (txt) this.bcast({ t: 'chat', n: sl.name, tm: sl.team, m: txt }); break; }
      case 'fall': if (c && c.alive && m.v > 9.5 && m.v < 40) Combat.fallDamage(c, +m.v); break;
      case 'ld': sl.pri = m.pri === 'akm' ? 'akm' : 'm4'; break;
      case 'ping': sl.rtt = clamp(+m.rtt || sl.rtt, 0, 2000); this.send(sl, { t: 'pong', c: m.c, T: Game.time }); break;
    }
  },
  rollLoot(c, p) {
    if (p.type === 'med') {
      const got = []; const add = (k, n) => { c.inv[k] = (c.inv[k] || 0) + n; got.push(ITEMS[k].ru + ' ×' + n); };
      add('bandage', rndi(1, 2)); if (Math.random() < 0.6) add('tourniquet', 1); if (Math.random() < 0.5) add('splint', 1); if (Math.random() < 0.6) add('pills', 1);
      if (Math.random() < 0.7) { const m = rndi(40, 90); c.inv.medPool += m; got.push('Аптечка +' + m); }
      if (Math.random() < 0.4) { c.inv.frag++; got.push('Осколочная'); }
      return got.join(', ');
    }
    if (Math.random() < 0.4) c.inv.flash++;
    return 'Магазины: ×2 + пистолетный';
  },
  /* ---------- рассылка ---------- */
  snapshots(dt) {
    this.snapT -= dt; this.vitT -= dt; this.sbT -= dt;
    if (!this.M) return;
    if (this.snapT <= 0) {
      this.snapT = 1 / this.cfg.snapHz;
      const ents = []; for (const c of Game.combatants) if (c.alive) ents.push(c);
      const gl = Grenades.list.map(g => [g.id, g.kind === 'flash' ? 1 : 0, +g.x.toFixed(2), +g.y.toFixed(2), +g.z.toFixed(2), +g.vx.toFixed(1), +g.vy.toFixed(1), +g.vz.toFixed(1), +g.fuse.toFixed(2)]);
      const pk = [];
      for (const s of this.humans()) {
        const e = []; for (const c of ents) if (c !== s.c) e.push([c.id, NET.pack(c)]);
        this.send(s, { t: 'snap', T: +Game.time.toFixed(3), e, g: gl, ack: s.lastSt });
      }
    }
    if (this.vitT <= 0) {
      this.vitT = 0.1;
      for (const s of this.humans()) if (s.c) this.send(s, { t: 'vit', v: NET.vitals(s.c), al: s.c.alive ? 1 : 0 });
    }
    if (this.sbT <= 0) { this.sbT = 1; this.sendBoard(false); }
  },
  sendBoard(force) {
    const M = this.M; if (!M) return;
    const rows = this.slots.map(s => [s.pid, s.name, s.team, s.kills, s.deaths, s.score, s.human ? Math.round(s.rtt) : 0, s.human ? 0 : 1, s.c && s.c.alive ? 1 : 0, s.c ? s.c.id : 0]);
    const K = M.koth; let ex = null;
    if (K) ex = { sp: K.spots[K.i], r: K.r, own: K.owner, prog: +Math.max(0, K.prog).toFixed(2), cap: K.cap === undefined ? -1 : K.cap, mv: Math.round(K.mv) };
    const o = { t: 'sb', id: M.mode.id, ph: M.phase, tl: Math.max(0, Math.round(M.mode.time - M.t)), pt: Math.max(0, Math.round(M.phT)), sc: M.score, wave: M.wave, round: M.round, rows, ex, lim: M.mode.limit, ms: M.msg, w: M.winner, al: M.mode.id === 'elim' ? [0, 1].map(t => Game.combatants.filter(c => c.alive && c.team === t).length) : null, bots: Game.combatants.filter(c => c.alive && c.isBot).length };
    for (const s of this.humans()) this.send(s, Object.assign({ me: s.pid, rs: s.respT }, o));
  },
  tick(dt) {
    if (this.idle) return;
    // респаун предметов
    for (const p of World.pickups) if (p.taken && p.respT > 0) { p.respT -= dt; if (p.respT <= 0) { p.taken = false; this.bcast({ t: 'pk', i: World.pickups.indexOf(p), taken: false }); } }
    Game.update(dt);
    this.tickMatch(dt);
    this.snapshots(dt);
    for (const s of this.humans()) if (Game.time - (s.lastMsg || s.joinT) > 15 && this.kick) this.kick(s);
  },
};
const SFX_OK = { reload: 1, magout: 1, magin: 1, rack: 1, dry: 1, swap: 1, pin: 1, throw: 1, meleestart: 1, meleemiss: 1, jump: 1, mode: 1, healstart: 1, healdone: 1 };

// связь событий боя с сетью
Bus.on('death', e => { if (SV.M) SV.onDeath(e); });
Bus.on('hit', e => {
  if (!SV.M) return;
  const v = e.victim; if (!v) return;
  SV.bcast({ t: 'hit', v: v.id, a: e.attacker ? e.attacker.id : 0, part: e.part, dmg: Math.round(e.dmg), k: e.killed ? 1 : 0, blk: e.blocked ? 1 : 0, arm: e.armorHit ? 1 : 0, p: e.pos.map(q => +q.toFixed(2)), d: e.dir.map(q => +q.toFixed(2)), cart: e.cart === CART.frag ? 'frag' : e.cart === CART.knife ? 'knife' : undefined });
  if (v.slot && v.slot.human) SV.send(v.slot, { t: 'vit', v: NET.vitals(v), al: v.alive ? 1 : 0 });
});
Bus.on('shot', e => {
  if (!SV.M) return; const c = e.c;
  SV.bcast({ t: 'shot', e: c.id, p: e.pos.map(q => +q.toFixed(3)), d: e.dir.map(q => +q.toFixed(4)), wi: c.cur, tr: e.tr !== undefined ? e.tr : (c.shotCount % 4 === 0) }, c.slot && c.slot.human ? c.slot : undefined);
});
Bus.on('explode', e => { if (SV.M) SV.bcast({ t: 'boom', x: +e.x.toFixed(2), y: +e.y.toFixed(2), z: +e.z.toFixed(2), k: e.kind, o: e.owner ? e.owner.id : 0 }); });
for (const k of ['reload', 'magout', 'magin', 'rack', 'dry', 'swap', 'pin', 'throw', 'meleestart', 'meleemiss', 'mode', 'healstart', 'healdone', 'jump']) {
  Bus.on(k, e => { if (!SV.M) return; const c = e.c || e; if (!c || !c.id || c.isHuman) return; SV.bcast({ t: 'sfx', k, e: c.id }); });
}
Bus.on('meleehit', e => { if (SV.M) SV.bcast({ t: 'sfx', k: 'meleehit', e: e.v.id }); });

;globalThis.__SV = { SV, World, Game, NET, Bus, Combatant, Grenades };
