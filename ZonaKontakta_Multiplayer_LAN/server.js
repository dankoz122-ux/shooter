const express = require('express');
const http = require('http');
const path = require('path');
const os = require('os');
const { Server } = require('socket.io');

const app = express();
const server = http.createServer(app);
const io = new Server(server, { cors: { origin: '*' }, maxHttpBufferSize: 1e6 });
const PORT = Number(process.env.PORT || 3000);
const players = new Map();
let hostId = null;
let matchConfig = null;

app.use((req, res, next) => { res.setHeader('Access-Control-Allow-Origin', '*'); res.setHeader('Access-Control-Allow-Methods', 'GET, OPTIONS'); if (req.method === 'OPTIONS') return res.sendStatus(204); next(); });
app.use(express.static(path.join(__dirname, 'public')));
app.get('/health', (_req, res) => res.json({ ok: true, players: players.size, host: !!hostId }));
app.get('/api/server-info', (_req, res) => res.json({ ok: true, name: 'Зона контакта · LAN', players: players.size, host: !!hostId, port: PORT }));
function cleanName(value) { return String(value || 'Боец').replace(/[<>\u0000-\u001f]/g, '').trim().slice(0, 20) || 'Боец'; }
function safeNum(v, fallback=0, min=-250, max=250) { const n=Number(v); return Number.isFinite(n) ? Math.max(min, Math.min(max,n)) : fallback; }
function publicPlayer(p) { return { id:p.id, name:p.name, team:p.team, spawnIndex:p.spawnIndex, x:p.x, y:p.y, z:p.z, yaw:p.yaw, pitch:p.pitch, crouch:p.crouch, ads:p.ads, speed:p.speed, leanA:p.leanA, alive:p.alive, weapon:p.weapon, parts:p.parts, armorState:p.armorState }; }
function broadcastPlayers() { io.emit('players', [...players.values()].map(publicPlayer)); }
io.on('connection', socket => {
  socket.on('joinGame', data => {
    if (players.has(socket.id)) { const old=players.get(socket.id); socket.emit('joined', { id:socket.id, host:socket.id===hostId, team:old.team===2?'red':'blue', spawnIndex:old.spawnIndex, gameMode:(matchConfig&&matchConfig.gameMode)||'teamBots', config:matchConfig }); return; }
    if (!hostId) {
      hostId = socket.id;
      const requested = data && ['teamBots','pvp','coop'].includes(data.gameMode) ? data.gameMode : 'teamBots';
      matchConfig = { gameMode: requested, bots: requested==='pvp' ? 0 : Math.round(safeNum(data && data.bots,8,2,16)), difficulty: Math.round(safeNum(data && data.difficulty,1,0,3)), armor: Math.round(safeNum(data && data.armor,3,0,5)), weapon: data && data.weapon==='akm' ? 'akm' : 'm4' };
    }
    const team = matchConfig && matchConfig.gameMode==='coop' ? 'red' : (data && data.team === 'red' ? 'red' : 'blue');
    // Allocate a different deterministic waypoint index to each connected player.
    // The client map generates the same waypoint list, so each player can choose a clear spot.
    const usedSpawns = new Set([...players.values()].map(p => p.spawnIndex));
    let spawnIndex = 0;
    for (let candidate = 0; candidate < 90; candidate++) {
      const spaced = (candidate * 7) % 90;
      if (!usedSpawns.has(spaced)) { spawnIndex = spaced; break; }
    }
    const p = { id:socket.id, name:cleanName(data && data.name), team:team==='red'?2:1, spawnIndex, x:0,y:0,z:0,yaw:0,pitch:0,crouch:0,ads:0,speed:0,leanA:0,alive:true,weapon:(data && ['m4','akm','glock'].includes(data.weapon) ? data.weapon : 'm4') };
    players.set(socket.id,p);
    socket.emit('joined', { id:socket.id, host:socket.id===hostId, team:team, spawnIndex, gameMode:(matchConfig && matchConfig.gameMode)||'teamBots', config:matchConfig });
    // Send the complete roster to the newcomer as well as existing clients.
    socket.emit('players', [...players.values()].map(publicPlayer));
    broadcastPlayers();
    console.log(`${p.name} joined (${team})${socket.id===hostId?' [host]':''}`);
  });
  socket.on('playerState', data => {
    const p=players.get(socket.id); if(!p || !data) return;
    p.x=safeNum(data.x,0,-125,125); p.y=safeNum(data.y,0,-5,10); p.z=safeNum(data.z,0,-125,125);
    p.yaw=safeNum(data.yaw,0,-100,100); p.pitch=safeNum(data.pitch,0,-2,2);
    p.crouch=safeNum(data.crouch,0,0,1); p.ads=safeNum(data.ads,0,0,1); p.speed=safeNum(data.speed,0,0,20); p.leanA=safeNum(data.leanA,0,-1,1);
    p.alive=data.alive!==false; p.weapon=['m4','akm','glock'].includes(data.weapon) ? data.weapon : (p.weapon || 'm4'); if(data.parts && typeof data.parts==='object') p.parts=data.parts; if(data.armorState && typeof data.armorState==='object') p.armorState=data.armorState;
    socket.broadcast.emit('playerState',publicPlayer(p));
  });
  socket.on('botsState', list => {
    if(socket.id!==hostId || !Array.isArray(list)) return;
    const clean=list.slice(0,32).map(b=>({ id:String(b.id||'').slice(0,24),name:cleanName(b.name),team:safeNum(b.team,1,0,20),x:safeNum(b.x,0,-125,125),y:safeNum(b.y,0,-5,10),z:safeNum(b.z,0,-125,125),yaw:safeNum(b.yaw,0,-100,100),pitch:safeNum(b.pitch,0,-2,2),crouch:safeNum(b.crouch,0,0,1),ads:safeNum(b.ads,0,0,1),speed:safeNum(b.speed,0,0,20),leanA:safeNum(b.leanA,0,-1,1),alive:b.alive!==false,parts:b.parts,armorState:b.armorState,weapon:'m4' }));
    socket.broadcast.emit('botsState',clean);
  });
  socket.on('hitState', hit => {
    if(!players.has(socket.id) || !hit || !hit.target || !['player','bot'].includes(hit.target.type)) return;
    if(hit.target.type==='player' && !players.has(String(hit.target.id))) return;
    // LAN prototype: state is relayed to all clients; the owning client performs the local ballistics calculation.
    const packet={ target:{type:hit.target.type,id:String(hit.target.id).slice(0,32)}, part:String(hit.part||'thorax').slice(0,20), alive:hit.alive===false?false:true, parts:hit.parts, armorState:hit.armorState };
    io.emit('hitState',packet);
  });
  socket.on('disconnect', () => {
    if(players.delete(socket.id)) { io.emit('playerLeft',socket.id); if(hostId===socket.id) { hostId=null; matchConfig=null; io.emit('serverNotice','Хост отключился. Матч завершён — обновите страницу и создайте новый матч.'); for (const id of [...players.keys()]) { const peer=io.sockets.sockets.get(id); if(peer) peer.disconnect(true); } players.clear(); } if(players.size===0) { hostId=null; matchConfig=null; } broadcastPlayers(); console.log(`disconnect ${socket.id}`); }
  });
});
server.listen(PORT, '0.0.0.0', () => {
  console.log('==================================================');
  console.log(' ЗОНА КОНТАКТА — LAN СЕРВЕР ЗАПУЩЕН');
  console.log(` На этом ПК: http://localhost:${PORT}`);
  const nets = os.networkInterfaces(); const ips = [];
  for (const list of Object.values(nets)) for (const item of (list || [])) if (item.family === 'IPv4' && !item.internal && !item.address.startsWith('169.254.')) ips.push(item.address);
  console.log(' Адреса для других ПК в этой сети:');
  if (ips.length) for (const ip of [...new Set(ips)]) console.log(`   http://${ip}:${PORT}`); else console.log('   IP не найден — проверь Wi-Fi/Ethernet и выполни ipconfig');
  console.log(' Не закрывай это окно, пока играете.');
  console.log('==================================================');
});
