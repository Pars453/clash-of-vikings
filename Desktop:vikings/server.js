'use strict';
/*
 * Clash of Vikings - game + online matchmaking server.
 *
 * Zero dependencies: only Node built-ins, so there is NO node_modules and
 * nothing to `npm install`.  Needs Node 14 or newer.
 *
 *     node server.js              ->  http://localhost:3000
 *     PORT=8080 node server.js    ->  another port
 *
 * The server never simulates the battle.  It pairs two players and then runs
 * a lockstep clock: every TURN_MS it broadcasts a numbered "turn" holding the
 * cards the players dropped since the previous turn.  Both browsers feed the
 * same turns into the same deterministic game, so the two screens stay
 * identical.
 */
const http = require('http');
const crypto = require('crypto');
const fs = require('fs');
const os = require('os');
const path = require('path');

const PORT = Number(process.env.PORT) || 3000;
const TURN_MS = Number(process.env.TURN_MS) || 50;     // one turn = 3 game ticks of 1/60 s
const GAME_FILE = path.join(__dirname, 'index.html');
const MAX_MATCH_MS = 6 * 60 * 1000;                    // a battle lasts 3 minutes; this is only a safety net
const END_GRACE_MS = 20 * 1000;                        // keep feeding turns to a player who is still catching up
const MAX_MSG = 16 * 1024;
const WS_GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';

/* ---------------------------------------------------------------- HTTP */

const server = http.createServer((req, res) => {
  const url = (req.url || '/').split('?')[0];
  if (url === '/' || url === '/index.html') {
    fs.readFile(GAME_FILE, (err, buf) => {
      if (err) {
        res.writeHead(500, { 'Content-Type': 'text/plain' });
        res.end('index.html must be in the same folder as server.js');
        return;
      }
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-cache' });
      res.end(buf);
    });
  } else if (url === '/healthz') {
    res.writeHead(200, { 'Content-Type': 'text/plain' });
    res.end('ok');
  } else {
    res.writeHead(404, { 'Content-Type': 'text/plain' });
    res.end('Not found');
  }
});

/* ----------------------------------------------- minimal WebSocket (RFC 6455) */

function frame(opcode, payload) {
  const n = payload.length;
  let head;
  if (n < 126) head = Buffer.from([0x80 | opcode, n]);
  else if (n < 65536) { head = Buffer.alloc(4); head[0] = 0x80 | opcode; head[1] = 126; head.writeUInt16BE(n, 2); }
  else { head = Buffer.alloc(10); head[0] = 0x80 | opcode; head[1] = 127; head.writeBigUInt64BE(BigInt(n), 2); }
  return Buffer.concat([head, payload]);
}
const textFrame = (s) => frame(0x1, Buffer.from(s));
const closeFrame = (code) => frame(0x8, Buffer.from([code >> 8, code & 255]));
const PING = frame(0x9, Buffer.alloc(0));

const clients = new Set();
let waiting = null;                                   // the player searching for an opponent

class Client {
  constructor(socket) {
    this.socket = socket;
    this.buf = Buffer.alloc(0);
    this.parts = [];
    this.partLen = 0;
    this.binary = false;
    this.alive = true;
    this.dead = false;
    this.hello = null;
    this.match = null;
    this.side = 0;
    this.ended = false;
    clients.add(this);
    socket.on('data', (d) => this.onData(d));
    // http.Server keeps half-closed sockets open, so a vanished browser would
    // otherwise stay "connected" (and could be matched) until the next heartbeat.
    socket.on('end', () => this.terminate());
    socket.on('close', () => this.drop());
    socket.on('error', () => this.drop());
  }

  raw(buf) { if (!this.dead && this.socket.writable) this.socket.write(buf); }
  send(obj) { this.raw(textFrame(JSON.stringify(obj))); }

  close(code) {
    if (this.dead) return;
    try { this.socket.end(closeFrame(code)); } catch (e) { /* already gone */ }
    this.drop();
    setTimeout(() => this.socket.destroy(), 1000).unref();
  }

  terminate() { this.drop(); this.socket.destroy(); }

  drop() {
    if (this.dead) return;
    this.dead = true;
    clients.delete(this);
    if (waiting === this) waiting = null;
    leave(this);
  }

  onData(chunk) {
    this.alive = true;
    this.buf = this.buf.length ? Buffer.concat([this.buf, chunk]) : chunk;
    for (;;) {
      const b = this.buf;
      if (b.length < 2) return;
      const fin = (b[0] & 0x80) !== 0;
      const rsv = b[0] & 0x70;
      const op = b[0] & 0x0f;
      const masked = (b[1] & 0x80) !== 0;
      let len = b[1] & 0x7f;
      let off = 2;
      if (rsv || !masked) return this.close(1002);                 // browsers always mask
      if (len === 126) { if (b.length < 4) return; len = b.readUInt16BE(2); off = 4; }
      else if (len === 127) {
        if (b.length < 10) return;
        if (b.readUInt32BE(2) !== 0) return this.close(1009);
        len = b.readUInt32BE(6); off = 10;
      }
      if (len > MAX_MSG) return this.close(1009);
      if (b.length < off + 4 + len) return;                        // wait for the rest
      const data = Buffer.allocUnsafe(len);
      for (let i = 0; i < len; i++) data[i] = b[off + 4 + i] ^ b[off + (i & 3)];
      this.buf = b.subarray(off + 4 + len);
      if (!this.onFrame(op, fin, data)) return;
    }
  }

  onFrame(op, fin, data) {
    if (op === 0x8) { this.close(1000); return false; }
    if (op === 0x9) { this.raw(frame(0xA, data)); return true; }   // ping -> pong
    if (op === 0xA) return true;                                    // pong
    if (op === 0x0 || op === 0x1 || op === 0x2) {
      if (op === 0x0) { if (!this.parts.length) { this.close(1002); return false; } }
      else { if (this.parts.length) { this.close(1002); return false; } this.binary = op === 0x2; }
      this.parts.push(data);
      this.partLen += data.length;
      if (this.partLen > MAX_MSG) { this.close(1009); return false; }
      if (fin) {
        const msg = Buffer.concat(this.parts);
        this.parts = [];
        this.partLen = 0;
        if (!this.binary) this.message(msg.toString('utf8'));
      }
      return true;
    }
    this.close(1002);
    return false;
  }

  message(text) {
    let m;
    try { m = JSON.parse(text); } catch (e) { return; }
    if (!m || typeof m !== 'object') return;
    switch (m.t) {
      case 'find': find(this, m); break;
      case 'cancel': if (waiting === this) waiting = null; break;
      case 'p': playCard(this, m); break;
      case 'h': checkHash(this, m); break;
      case 'end': finished(this); break;
      case 'leave': leave(this); break;
      default: break;
    }
  }
}

server.on('upgrade', (req, socket, head) => {
  const key = req.headers['sec-websocket-key'];
  const isWs = String(req.headers.upgrade || '').toLowerCase() === 'websocket';
  if (!key || !isWs || (req.url || '').split('?')[0] !== '/ws') {
    socket.end('HTTP/1.1 400 Bad Request\r\nConnection: close\r\n\r\n');
    return;
  }
  const accept = crypto.createHash('sha1').update(key + WS_GUID).digest('base64');
  socket.write(
    'HTTP/1.1 101 Switching Protocols\r\n' +
    'Upgrade: websocket\r\n' +
    'Connection: Upgrade\r\n' +
    'Sec-WebSocket-Accept: ' + accept + '\r\n\r\n'
  );
  socket.setNoDelay(true);
  const c = new Client(socket);
  if (head && head.length) c.onData(head);
});

/* ----------------------------------------------------- matchmaking & turns */

// The server only bounds sizes; each game validates the real content itself.
const cleanDeck = (d) => (Array.isArray(d) ? d.slice(0, 8).map((x) => String(x).replace(/[^a-z0-9_]/g, '').slice(0, 20)) : []);
const cleanRune = (r) => (/^[a-z]{0,12}$/.test(String(r || '')) ? String(r || '') : '');
function cleanLv(o) {
  const out = {};
  if (o && typeof o === 'object') {
    for (const k of Object.keys(o).slice(0, 48)) {
      const v = Number(o[k]);
      if (/^[a-z0-9_]{1,20}$/.test(k) && Number.isInteger(v) && v >= 1 && v <= 5) out[k] = v;
    }
  }
  return out;
}

function find(c, m) {
  if (c.match) leave(c);                               // searching again after a battle
  if (waiting === c) return;
  c.hello = { deck: cleanDeck(m.deck), rune: cleanRune(m.rune), lv: cleanLv(m.lv) };
  c.ended = false;
  if (waiting && !waiting.dead) {
    const a = waiting;
    waiting = null;
    startMatch(a, c);
  } else {
    waiting = c;
    c.send({ t: 'wait' });
  }
}

function startMatch(a, b) {
  const players = Math.random() < 0.5 ? [a, b] : [b, a];            // random sides
  const m = {
    players, n: 0, cmds: [[], []], hashes: new Map(),
    timer: null, endTimer: null, closed: false, t0: Date.now(),
  };
  players.forEach((p, i) => { p.match = m; p.side = i; p.ended = false; });
  const start = {
    t: 'start',
    seed: 1 + Math.floor(Math.random() * 0x7fffffff),
    decks: players.map((p) => p.hello.deck),
    runes: players.map((p) => p.hello.rune),
    lv: players.map((p) => p.hello.lv),
  };
  players.forEach((p, i) => p.send(Object.assign({ side: i }, start)));
  m.timer = setInterval(() => turn(m), TURN_MS);
}

function turn(m) {
  if (m.closed) return;
  if (Date.now() - m.t0 > MAX_MATCH_MS) { closeMatch(m); return; }
  m.n += 1;
  const c = [];
  for (let s = 0; s < 2; s++) for (const x of m.cmds[s]) c.push([s, ...x]);   // same order for everyone
  m.cmds = [[], []];
  const f = textFrame(JSON.stringify({ t: 'T', n: m.n, c }));
  for (const p of m.players) p.raw(f);
}

function playCard(c, m) {
  const mt = c.match;
  if (!mt || mt.closed || c.ended) return;
  const { i, id, x, y } = m;
  if (!Number.isInteger(i) || i < 0 || i > 3) return;
  if (typeof id !== 'string' || id.length > 20) return;
  if (!Number.isFinite(x) || !Number.isFinite(y)) return;
  const q = mt.cmds[c.side];
  if (q.length >= 4) return;                                        // flood guard
  q.push([i, id, Math.round(x * 10) / 10, Math.round(y * 10) / 10]);
}

// Players report a checksum of their game every few seconds.  If the two
// disagree the games have drifted apart, so stop instead of lying to them.
function checkHash(c, m) {
  const mt = c.match;
  if (!mt || mt.closed || !Number.isInteger(m.n) || !Number.isInteger(m.h)) return;
  const e = mt.hashes.get(m.n) || [null, null];
  e[c.side] = m.h;
  if (e[0] !== null && e[1] !== null) {
    mt.hashes.delete(m.n);
    if (e[0] !== e[1]) {
      console.error('[desync] match went out of sync at turn ' + m.n);
      for (const p of mt.players) if (!p.dead) p.send({ t: 'bad', n: m.n });
      closeMatch(mt);
    }
  } else {
    mt.hashes.set(m.n, e);
    if (mt.hashes.size > 50) mt.hashes.delete(mt.hashes.keys().next().value);
  }
}

// A player's game reached its end (king down or time up).
function finished(c) {
  const mt = c.match;
  if (!mt || mt.closed) return;
  c.ended = true;
  if (mt.players.every((p) => p.ended || p.dead)) closeMatch(mt);
  else if (!mt.endTimer) mt.endTimer = setTimeout(() => closeMatch(mt), END_GRACE_MS);
}

// Leaving before the end is a forfeit; leaving after the end is not.
function leave(c) {
  const mt = c.match;
  if (!mt) return;
  c.match = null;
  if (mt.closed) return;
  if (!c.ended) {
    const other = mt.players[1 - c.side];
    if (other && other.match === mt && !other.dead) other.send({ t: 'left' });
    closeMatch(mt);
  } else if (mt.players.every((p) => p.match !== mt)) {
    closeMatch(mt);
  }
}

function closeMatch(m) {
  if (m.closed) return;
  m.closed = true;
  clearInterval(m.timer);
  clearTimeout(m.endTimer);
  for (const p of m.players) if (p.match === m) p.match = null;
}

// Keep idle connections alive through proxies and drop dead ones.
setInterval(() => {
  for (const c of clients) {
    if (!c.alive) { c.terminate(); continue; }
    c.alive = false;
    c.raw(PING);
  }
}, 25000).unref();

/* --------------------------------------------------------------- start */

server.on('error', (e) => {
  if (e.code === 'EADDRINUSE') {
    console.error('Port ' + PORT + ' is already in use. Close the other server (the old socket.io one?) or use another port, e.g. PORT=' + (PORT + 1) + ' node server.js');
  } else {
    console.error(e);
  }
  process.exit(1);
});

server.listen(PORT, () => {
  console.log('Clash of Vikings server is running');
  console.log('  This computer : http://localhost:' + PORT);
  for (const list of Object.values(os.networkInterfaces())) {
    for (const i of list || []) {
      if ((i.family === 'IPv4' || i.family === 4) && !i.internal) console.log('  Same Wi-Fi    : http://' + i.address + ':' + PORT);
    }
  }
});
