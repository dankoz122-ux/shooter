'use strict';
/* ЗОНА КОНТАКТА — игровой сервер (без внешних зависимостей).
   Запуск: node server.js   (Render задаёт PORT автоматически) */
const http = require('http'), crypto = require('crypto'), fs = require('fs'), path = require('path'), vm = require('vm'), zlib = require('zlib');

const PORT = +process.env.PORT || 8080;
const TICK = 30;
// ---- загрузка общей симуляции (та же, что в браузере) ----
vm.runInThisContext(fs.readFileSync(path.join(__dirname, 'sim.js'), 'utf8'), { filename: 'sim.js' });
const { SV, World, Game, NET, Bus } = globalThis.__SV;
World.generate();
Game.resetNet(); Game.noRagdoll = true; Game.lagComp = true; Game.noFF = true; Game.netServer = true;
const env = process.env;
if (env.ROTATION) SV.cfg.rotation = env.ROTATION.split(',').map(s => s.trim()).filter(s => ['tdm', 'ffa', 'elim', 'koth', 'coop'].includes(s));
if (!SV.cfg.rotation.length) SV.cfg.rotation = ['tdm'];
if (env.DEV) SV.cfg.dev = true;
if (env.TARGET) SV.cfg.target = Math.max(2, Math.min(20, +env.TARGET));
if (env.DIFF) SV.cfg.diff = Math.max(0, Math.min(3, +env.DIFF));
if (env.ARMOR) SV.cfg.armor = +env.ARMOR;
if (env.MAX_PLAYERS) SV.cfg.maxPlayers = Math.max(1, Math.min(16, +env.MAX_PLAYERS));
if (env.SNAP_HZ) SV.cfg.snapHz = Math.max(10, Math.min(30, +env.SNAP_HZ));
const mapSum = (() => { let s = 0; World.boxes.forEach((b, i) => { s += (b.x0 + b.x1 + b.z0 + b.z1 + b.y1) * (i % 7 + 1); }); return Math.round(s) + ':' + Math.round(World.H(30, -20) * 100) + ':' + World.pickups.length; })();
console.log('карта', mapSum, '| режимы:', SV.cfg.rotation.join(','), '| порт', PORT);

// ---- HTTP ----
const pub = path.join(__dirname, 'public', 'index.html');
let html = null, htmlGz = null;
const loadHtml = () => { try { html = fs.readFileSync(pub); htmlGz = zlib.gzipSync(html, { level: 6 }); } catch (e) { html = Buffer.from('Нет public/index.html'); htmlGz = null; } };
loadHtml();
const server = http.createServer((req, res) => {
  const u = req.url.split('?')[0];
  if (u === '/healthz') { res.writeHead(200, { 'Content-Type': 'text/plain' }); return res.end('ok'); }
  if (u === '/info') { res.writeHead(200, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' }); return res.end(JSON.stringify({ players: SV.humans().length, max: SV.cfg.maxPlayers, mode: SV.M ? SV.M.mode.id : null, map: mapSum })); }
  if (u === '/' || u === '/index.html') {
    const gz = htmlGz && /gzip/.test(req.headers['accept-encoding'] || '');
    res.writeHead(200, Object.assign({ 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-cache' }, gz ? { 'Content-Encoding': 'gzip' } : {}));
    return res.end(gz ? htmlGz : html);
  }
  res.writeHead(404); res.end('404');
});

// ---- WebSocket (RFC 6455, только то, что нужно) ----
const GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';
function wsSend(sock, str) {
  if (sock.destroyed || !sock.writable) return;
  const b = Buffer.from(str, 'utf8'), n = b.length;
  let h;
  if (n < 126) h = Buffer.from([0x81, n]);
  else if (n < 65536) { h = Buffer.alloc(4); h[0] = 0x81; h[1] = 126; h.writeUInt16BE(n, 2); }
  else { h = Buffer.alloc(10); h[0] = 0x81; h[1] = 127; h.writeBigUInt64BE(BigInt(n), 2); }
  sock.write(Buffer.concat([h, b]));
}
function wsCtl(sock, op, payload) { if (sock.destroyed) return; const p = payload || Buffer.alloc(0); sock.write(Buffer.concat([Buffer.from([0x80 | op, p.length]), p])); }

server.on('upgrade', (req, sock) => {
  const key = req.headers['sec-websocket-key'];
  if (!key || (req.headers.upgrade || '').toLowerCase() !== 'websocket') { sock.destroy(); return; }
  const acc = crypto.createHash('sha1').update(key + GUID).digest('base64');
  sock.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ' + acc + '\r\n\r\n');
  sock.setNoDelay(true); sock.setKeepAlive(true, 20000);
  const conn = { sock, buf: Buffer.alloc(0), frag: [], slot: null, msgs: 0, mt: Date.now(), alive: true };
  sock.on('data', d => {
    conn.buf = conn.buf.length ? Buffer.concat([conn.buf, d]) : d;
    if (conn.buf.length > 1 << 20) { sock.destroy(); return; }
    try { parse(conn); } catch (e) { console.log('ws parse', e.message); sock.destroy(); }
  });
  const gone = () => { if (!conn.alive) return; conn.alive = false; if (conn.slot) { try { SV.leave(conn.slot); } catch (e) { console.log('leave', e); } conn.slot = null; } };
  sock.on('close', gone); sock.on('error', gone); sock.on('end', gone);
  conn.ping = setInterval(() => { if (conn.alive) wsCtl(sock, 9); }, 20000);
  sock.on('close', () => clearInterval(conn.ping));
});
function parse(conn) {
  for (;;) {
    const b = conn.buf; if (b.length < 2) return;
    const fin = !!(b[0] & 0x80), op = b[0] & 15, masked = !!(b[1] & 0x80); let len = b[1] & 127, off = 2;
    if (len === 126) { if (b.length < 4) return; len = b.readUInt16BE(2); off = 4; }
    else if (len === 127) { if (b.length < 10) return; len = Number(b.readBigUInt64BE(2)); off = 10; }
    if (len > 1 << 17) { conn.sock.destroy(); return; }
    if (!masked) { conn.sock.destroy(); return; }
    if (b.length < off + 4 + len) return;
    const mask = b.slice(off, off + 4), data = Buffer.alloc(len);
    for (let i = 0; i < len; i++) data[i] = b[off + 4 + i] ^ mask[i & 3];
    conn.buf = b.slice(off + 4 + len);
    if (op === 8) { try { wsCtl(conn.sock, 8); } catch (e) { } conn.sock.end(); return; }
    if (op === 9) { wsCtl(conn.sock, 10, data); continue; }
    if (op === 10) continue;
    if (op === 0 || op === 1) {
      conn.frag.push(data);
      if (fin) { const s = Buffer.concat(conn.frag).toString('utf8'); conn.frag = []; onMessage(conn, s); }
    }
  }
}
function onMessage(conn, s) {
  const now = Date.now();
  if (now - conn.mt > 1000) { conn.mt = now; conn.msgs = 0; }
  if (++conn.msgs > 220) { conn.sock.destroy(); return; }
  let m; try { m = JSON.parse(s); } catch (e) { return; }
  if (!m || typeof m.t !== 'string') return;
  if (!conn.slot) {
    if (m.t !== 'hello') return;
    if (m.v !== NET.VER) { wsSend(conn.sock, JSON.stringify({ t: 'err', m: 'Версия клиента не совпадает с сервером. Обновите страницу.' })); conn.sock.end(); return; }
    const sl = SV.join(null, null, m.name, m.pri);
    if (!sl) { wsSend(conn.sock, JSON.stringify({ t: 'err', m: 'Сервер заполнен' })); conn.sock.end(); return; }
    sl.ws = conn.sock; conn.slot = sl;
    const ents = Game.combatants.filter(c => c !== sl.c).map(c => Object.assign(NET.info(c), { st: NET.pack(c), al: c.alive ? 1 : 0 }));
    const sp = sl.c ? { e: sl.c.id, x: sl.c.x, z: sl.c.z, yaw: sl.c.yaw, pri: sl.pri, team: sl.team, inv: sl.c.inv } : null;
    wsSend(conn.sock, JSON.stringify({ t: 'welcome', pid: sl.pid, T: Game.time, map: mapSum, snapHz: SV.cfg.snapHz, spawn: sp, ents, pk: World.pickups.map((p, i) => p.taken ? i : -1).filter(i => i >= 0), name: sl.name }));
    SV.bcast({ t: 'chat', n: '', m: sl.name + ' подключился' }, sl);
    SV.sendBoard(true);
    if (SV.M) wsSend(conn.sock, JSON.stringify({ t: 'match', id: SV.M.mode.id, ru: SV.M.mode.ru, team: SV.M.mode.team, coop: !!SV.M.mode.coop }));
    console.log('+', sl.name, '(' + SV.humans().length + ')');
    return;
  }
  try { SV.msg(conn.slot, m); } catch (e) { console.log('msg error', m.t, e.stack); }
}
SV.kick = s => { if (s.ws) s.ws.destroy(); };
SV.out = (slot, obj) => { if (slot.ws) wsSend(slot.ws, JSON.stringify(obj)); };
SV.outRaw = (slot, str) => { if (slot.ws) wsSend(slot.ws, str); };

// ---- цикл симуляции ----
let last = Date.now(), acc = 0;
setInterval(() => {
  const now = Date.now(); acc += Math.min(0.25, (now - last) / 1000); last = now;
  const step = 1 / TICK; let n = 0;
  while (acc >= step && n++ < 4) { acc -= step; try { SV.tick(step); } catch (e) { console.log('tick error', e.stack); } }
  if (acc > step * 4) acc = 0;
}, 1000 / TICK / 2);

server.listen(PORT, () => console.log('Сервер слушает порт', PORT));
process.on('uncaughtException', e => console.log('uncaught', e.stack));
