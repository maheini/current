'use strict';
// Sägewerk-Panik: liefert die Seiten aus /public und vermittelt das Duell über WebSocket (/ws).
// Es gibt genau ein Spiel für alle: zwei Plätze, alle anderen schauen zu. Keine Datenbank, alles im Speicher.
// Runde 1, 3, 5 …: Platz 1 sägt mit Wechselstrom, Platz 2 mit Gleichstrom. Danach wird getauscht.
const http = require('http');
const fs = require('fs');
const path = require('path');
const { WebSocketServer } = require('ws');

const PORT = Number(process.env.PORT) || 3000;
const PUBLIC = path.join(__dirname, 'public');
const MAX_CLIENTS = 400;
const COUNTDOWN_MS = 3000;
const ROUND_S = Number(process.env.ROUND_S) || 60;
const ROUND_MAX_MS = ROUND_S * 1000 + 8000;   // falls eine Meldung nie ankommt
const IDLE_MS = 180000;                        // so lange darf ein Platz blockiert werden, während die andere Person bereit ist

const TYPES = {
  '.html': 'text/html; charset=utf-8',
  '.js': 'text/javascript; charset=utf-8',
  '.css': 'text/css; charset=utf-8',
  '.svg': 'image/svg+xml',
  '.png': 'image/png',
  '.ico': 'image/x-icon',
  '.json': 'application/json; charset=utf-8',
};
const ALIASES = { '/': '/index.html', '/erklaerung': '/erklaerung.html' };

const server = http.createServer((req, res) => {
  if (req.method !== 'GET' && req.method !== 'HEAD') { res.writeHead(405); res.end(); return; }
  let p;
  try { p = decodeURIComponent(new URL(req.url, 'http://localhost').pathname); } catch { res.writeHead(400); res.end(); return; }
  if (p === '/healthz') { res.writeHead(200, { 'Content-Type': 'text/plain' }); res.end('ok'); return; }
  p = ALIASES[p] || p;
  const file = path.normalize(path.join(PUBLIC, p));
  if (!file.startsWith(PUBLIC + path.sep)) { res.writeHead(403); res.end(); return; }
  if (path.extname(file) === '.html') {
    fs.readFile(file, 'utf8', (err, html) => {
      if (err) { res.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8' }); res.end('Nicht gefunden'); return; }
      // neue Version von JS/CSS = neue URL, damit kein Browser oder Proxy alte Dateien behält
      html = html.replace(/(src|href)="(game\.js|base\.css)"/g, (m, a, f) => {
        let v = 0; try { v = Math.floor(fs.statSync(path.join(PUBLIC, f)).mtimeMs); } catch (_) {}
        return `${a}="${f}?v=${v}"`;
      });
      res.writeHead(200, { 'Content-Type': TYPES['.html'], 'Cache-Control': 'no-store', 'X-Content-Type-Options': 'nosniff' });
      res.end(req.method === 'HEAD' ? undefined : html);
    });
    return;
  }
  fs.stat(file, (err, st) => {
    if (err || !st.isFile()) {
      res.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8' });
      res.end('Nicht gefunden');
      return;
    }
    res.writeHead(200, {
      'Content-Type': TYPES[path.extname(file)] || 'application/octet-stream',
      'Content-Length': st.size,
      'Cache-Control': 'no-cache',
      'X-Content-Type-Options': 'nosniff',
    });
    if (req.method === 'HEAD') { res.end(); return; }
    fs.createReadStream(file).pipe(res);
  });
});

/* ---------- Das eine Spiel ---------- */
const game = {
  state: 'lobby', round: 0, seed: 0, players: [null, null], viewers: new Set(), history: [],
  done: [null, null], last: [null, null], timer: null, startedAt: 0,
};
const cleanName = n => (typeof n === 'string' ? n.replace(/[\u0000-\u001f\u007f<>]/g, '').trim().slice(0, 16) : '');
const num = (v, lo, hi) => { const x = Number(v); return Number.isFinite(x) ? Math.max(lo, Math.min(hi, x)) : lo; };
const int = (v, lo, hi) => Math.round(num(v, lo, hi));
const rolesFor = n => (n % 2 === 1 ? ['ac', 'dc'] : ['dc', 'ac']);
const busy = () => game.state === 'countdown' || game.state === 'playing';

function send(ws, msg) { if (ws && ws.readyState === 1) ws.send(JSON.stringify(msg)); }
function everyone() {
  const list = [...game.viewers];
  game.players.forEach(p => { if (p) list.push(p.ws); });
  return list;
}
function info(ws) {
  return {
    t: 'game', state: game.state, round: game.round, dur: ROUND_S,
    players: game.players.map(p => (p ? { name: p.name, ready: p.ready } : null)),
    viewers: game.viewers.size, history: game.history, you: ws.slot,
  };
}
function broadcastInfo() { for (const ws of everyone()) send(ws, info(ws)); }
function broadcast(msg) {
  const data = JSON.stringify(msg);
  for (const ws of everyone()) if (ws.readyState === 1) ws.send(data);
}
function toLobby(state) {
  clearTimeout(game.timer);
  game.timer = null;
  game.state = state;
  game.players.forEach(p => { if (p) { p.ready = false; p.idleSince = Date.now(); } });
}

function startRound() {
  clearTimeout(game.timer);
  game.state = 'countdown';
  game.round++;
  game.seed = Math.floor(Math.random() * 2147483647);
  game.done = [null, null];
  game.last = [null, null];
  game.players.forEach(p => { p.ready = false; });
  broadcast({ t: 'start', round: game.round, roles: rolesFor(game.round), seed: game.seed, delay: COUNTDOWN_MS, dur: ROUND_S });
  broadcastInfo();
  game.timer = setTimeout(() => {
    game.state = 'playing';
    game.startedAt = Date.now();
    game.timer = setTimeout(finishRound, ROUND_MAX_MS);
  }, COUNTDOWN_MS);
}
// Nach Ablauf der Zeit gewinnt, wer mehr Stämme durchgesägt hat
function finishRound() {
  if (game.state !== 'playing') return;
  const cuts = [0, 1].map(i => (game.done[i] ? game.done[i].c : game.last[i] ? game.last[i].c : 0));
  const winner = cuts[0] === cuts[1] ? -1 : cuts[0] > cuts[1] ? 0 : 1;
  const names = game.players.map((p, i) => (p ? p.name : 'Platz ' + (i + 1)));
  const entry = { n: game.round, names, roles: rolesFor(game.round), winner, cuts };
  game.history.push(entry);
  if (game.history.length > 30) game.history.shift();
  toLobby('result');
  broadcast({ t: 'result', ...entry });
  broadcastInfo();
}

function leaveSlot(ws, why) {
  if (ws.slot < 0) return;
  const p = game.players[ws.slot];
  game.players[ws.slot] = null;
  ws.slot = -1;
  if (busy()) {
    toLobby('lobby');
    broadcast({ t: 'aborted', msg: (p ? p.name : 'Jemand') + ' ' + why });
  }
}

const wss = new WebSocketServer({ server, path: '/ws', maxPayload: 4096 });
wss.on('connection', ws => {
  if (wss.clients.size > MAX_CLIENTS) { send(ws, { t: 'error', msg: 'Es sind gerade zu viele Leute da. Versucht es gleich nochmal.' }); ws.close(); return; }
  ws.isAlive = true;
  ws.slot = -1;
  ws.on('pong', () => { ws.isAlive = true; });
  game.viewers.add(ws);
  broadcastInfo();
  const bucket = { t: Date.now(), n: 0 };

  ws.on('message', data => {
    const now = Date.now();
    if (now - bucket.t > 1000) { bucket.t = now; bucket.n = 0; }
    if (++bucket.n > 80) return;
    let m;
    try { m = JSON.parse(data); } catch { return; }
    if (!m || typeof m.t !== 'string') return;
    const me = ws.slot >= 0 ? game.players[ws.slot] : null;

    switch (m.t) {
      case 'join': {
        if (me) return;
        const name = cleanName(m.name);
        if (!name) { send(ws, { t: 'error', msg: 'Gib zuerst deinen Namen ein.' }); return; }
        const free = game.players.findIndex(p => !p);
        if (free < 0) { send(ws, { t: 'error', msg: 'Beide Plätze sind besetzt. Du schaust zu, bis einer frei wird.' }); return; }
        game.viewers.delete(ws);
        ws.slot = free;
        game.players[free] = { ws, name, ready: false, idleSince: now, readySince: now };
        broadcastInfo();   // zuerst die Platznummer, dann der Start
        if (game.players.every(p => p && p.ready) && !busy()) startRound();
        break;
      }
      case 'ready': {
        if (!me || busy()) return;
        me.ready = true;
        me.readySince = now;
        if (game.players.every(p => p && p.ready)) startRound();
        else broadcastInfo();
        break;
      }
      case 'watch': {
        if (!me) return;
        leaveSlot(ws, 'schaut jetzt zu.');
        game.viewers.add(ws);
        broadcastInfo();
        break;
      }
      case 'state': {
        if (!me || game.state !== 'playing' || !m.s || typeof m.s !== 'object') return;
        const q = m.s;
        const s = {
          t: num(q.t, 0, 1e5), p: num(q.p, -1e7, 1e7), g: num(q.g, 0, 1), f: num(q.f, 0, 1), ph: int(q.ph, 0, 5), pt: num(q.pt, 0, 60), k: int(q.k, -1, 1e5),
          q: Array.isArray(q.q) ? q.q.slice(0, 6).map(i => int(i, 0, 1e5)) : [],
          c: int(q.c, 0, 1e5), x: int(q.x, 0, 1e5), a: q.a ? 1 : 0,
        };
        game.last[ws.slot] = s;
        const out = JSON.stringify({ t: 'peer', slot: ws.slot, s });
        for (const o of everyone()) if (o !== ws && o.readyState === 1) o.send(out);
        break;
      }
      case 'done': {
        if (!me || game.state !== 'playing' || game.done[ws.slot]) return;
        game.done[ws.slot] = { c: int(m.c, 0, 1e5) };
        if (game.done[0] && game.done[1]) finishRound();
        break;
      }
    }
  });
  ws.on('close', () => {
    leaveSlot(ws, 'hat das Spiel verlassen.');
    game.viewers.delete(ws);
    broadcastInfo();
  });
  ws.on('error', () => {});
});

// Wer einen Platz besetzt, aber nicht bereit wird, während die andere Person wartet, schaut wieder zu
setInterval(() => {
  if (busy()) return;
  const now = Date.now();
  let changed = false;
  game.players.forEach((p, i) => {
    const o = game.players[1 - i];
    if (p && !p.ready && o && o.ready && now - Math.max(p.idleSince, o.readySince || 0) > IDLE_MS) {
      send(p.ws, { t: 'error', msg: 'Du warst zu lange nicht bereit und schaust jetzt zu.' });
      game.players[i] = null;
      p.ws.slot = -1;
      game.viewers.add(p.ws);
      changed = true;
    }
  });
  if (changed) broadcastInfo();
}, 5000);

const heartbeat = setInterval(() => {
  for (const ws of wss.clients) {
    if (!ws.isAlive) { ws.terminate(); continue; }
    ws.isAlive = false;
    ws.ping();
  }
}, 20000);
wss.on('close', () => clearInterval(heartbeat));

server.listen(PORT, () => console.log(`Sägewerk-Panik läuft auf http://localhost:${PORT}`));
