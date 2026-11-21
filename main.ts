// A push-optimal Sokoban solver, written for sokoban-solver-01-run-20261121.
//
// Strategy (derived from the level structure in the kit's RULES.txt: a hallway with
// 1-4 rooms of 3-4 boxes each, boxes never leaving their room):
//   1. Split the level into its rooms: cut the hallway row's dead squares out of the
//      floor; each connected part holding boxes is one room, with its own goals.
//   2. Solve each room on its own with an A* over pushes (cost 1 per push), the
//      other rooms' boxes standing as walls, the player walking on from where the
//      last room left it. The rooms' optima add up to the level's P*.
//   3. A room's A* uses an admissible min-matching heuristic (each box's walking
//      distance to its assigned goal, ignoring boxes: one push moves one box one
//      step, so the matching sum lower-bounds the pushes left) and prunes three
//      deadlocks no solution can survive: dead squares (a box that can never be
//      pulled back onto a goal), wall lines with no goal on them, frozen boxes and
//      frozen 2x2 blocks. A plain push-BFS with the same pruning is the fallback
//      when A* exhausts its node budget.
//   4. If a level is no set of rooms, the same search runs on the whole level.
//
// Pure and deterministic: all budgets count search nodes, never the clock; no
// randomness; every tie breaks by a fixed order, so two runs write byte-identical
// answers. Node stdlib only, no network, no model calls.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Node budgets (never the clock): a room's A* first, then its BFS fallback.
const ASTAR_EXPANSIONS = 400_000;
const BFS_STATES = 400_000;
const WHOLE_LEVEL_EXPANSIONS = 800_000;

type Dir = readonly [number, number, string, string];
const DIRS: readonly Dir[] = [
  [0, -1, 'u', 'U'],
  [0, 1, 'd', 'D'],
  [-1, 0, 'l', 'L'],
  [1, 0, 'r', 'R'],
];

interface Level {
  w: number;
  h: number;
  wall: Uint8Array;
  goals: number[];
  boxes: number[];
  player: number;
}

/** Parse XSB text (# wall, space floor, . goal, $ box, * box on goal, @ player). */
function parseLevel(text: string): Level {
  const rows = text.split('\n').filter((r) => r.length > 0);
  const h = rows.length;
  const w = Math.max(...rows.map((r) => r.length));
  const wall = new Uint8Array(w * h).fill(1);
  const goals: number[] = [];
  const boxes: number[] = [];
  let player = -1;
  rows.forEach((row, y) => {
    for (let x = 0; x < row.length; x++) {
      const ch = row[x]!;
      const i = y * w + x;
      if (ch === '#') continue;
      wall[i] = 0;
      if (ch === '.' || ch === '*' || ch === '+') goals.push(i);
      if (ch === '$' || ch === '*') boxes.push(i);
      if (ch === '@' || ch === '+') player = i;
    }
  });
  // The outer frame is wall whatever it shows: nothing leaves the board.
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      if (x === 0 || y === 0 || x === w - 1 || y === h - 1) wall[y * w + x] = 1;
    }
  }
  return { w, h, wall, goals, boxes: boxes.sort((a, b) => a - b), player };
}

/** Walking distances from `from` over floor alone (walls only, boxes ignored). */
function bfsDist(lv: Level, from: number): Int32Array {
  const { w, wall } = lv;
  const dist = new Int32Array(wall.length).fill(-1);
  const queue = [from];
  dist[from] = 0;
  for (let qi = 0; qi < queue.length; qi++) {
    const p = queue[qi]!;
    for (const [dx, dy] of DIRS) {
      const q = p + dy * w + dx;
      if (!wall[q] && dist[q] < 0) {
        dist[q] = dist[p]! + 1;
        queue.push(q);
      }
    }
  }
  return dist;
}

/**
 * The squares from which a box alone can still reach a goal: pull every goal's
 * box backwards over open floor (a box at y can be pulled from x = y + d when
 * y - d is open floor too). A box off a live square is lost, whatever else moves.
 */
function liveSquares(lv: Level): Uint8Array {
  const { w, wall, goals } = lv;
  const live = new Uint8Array(wall.length);
  const queue = [...goals];
  for (const g of goals) live[g] = 1;
  for (let qi = 0; qi < queue.length; qi++) {
    const x = queue[qi]!;
    for (const [dx, dy] of DIRS) {
      const d = dy * w + dx;
      const y = x - d;
      if (!wall[y] && !wall[y - d] && !live[y]) {
        live[y] = 1;
        queue.push(y);
      }
    }
  }
  return live;
}

/**
 * Squares on a wall line with no goal on it and no way off it: a box pressed
 * against a wall can only slide along that wall (away from the wall needs the
 * player on the wall's square) and can never leave the floor run along the
 * wall, so with no goal on the run and no square in it where the wall ends
 * (where the box could step off the wall) it is dead. The run is the whole
 * floor run along the wall, not just the squares still against it: a box can
 * slide into the square where the wall ends and step off there.
 */
function wallDeadSquares(lv: Level): Uint8Array {
  const { w, wall, goals } = lv;
  const size = wall.length;
  const dead = new Uint8Array(size);
  const goalMask = new Uint8Array(size);
  for (const g of goals) goalMask[g] = 1;
  for (const [dx, dy] of DIRS) {
    const d = dy * w + dx;
    const p = dx === 0 ? 1 : w; // the slide axis, perpendicular to the wall side
    for (let i = 0; i < size; i++) {
      if (wall[i] || !wall[i + d] || goalMask[i]) continue;
      let hasGoal = false;
      let hasExit = false;
      for (let c = i + p; !wall[c]; c += p) {
        if (goalMask[c]) hasGoal = true;
        if (!wall[c + d]) hasExit = true;
      }
      for (let c = i - p; !wall[c]; c -= p) {
        if (goalMask[c]) hasGoal = true;
        if (!wall[c + d]) hasExit = true;
      }
      if (!hasGoal && !hasExit) dead[i] = 1;
    }
  }
  return dead;
}

/**
 * The squares the player reaches from `from` around walls and `occupied` boxes,
 * marked in `seen` with `stamp`; returns the lowest square of the region. A
 * region's lowest square names it: two regions sharing a lowest square would
 * share that square, so the name is unique.
 */
function reach(
  lv: Level,
  occupied: Uint8Array,
  from: number,
  seen: Int32Array,
  stamp: number,
  stack: Int32Array,
): number {
  const { w, wall } = lv;
  let low = from;
  let n = 0;
  stack[n++] = from;
  seen[from] = stamp;
  while (n > 0) {
    const p = stack[--n]!;
    if (p < low) low = p;
    for (let k = 0; k < 4; k++) {
      const q = k === 0 ? p - w : k === 1 ? p + w : k === 2 ? p - 1 : p + 1;
      if (wall[q] === 0 && occupied[q] === 0 && seen[q] !== stamp) {
        seen[q] = stamp;
        stack[n++] = q;
      }
    }
  }
  return low;
}

/** Whether the box just pushed to `t` sits in a frozen 2x2 block of walls and boxes with a box off its goal. */
function frozenBlock(lv: Level, occupied: Uint8Array, goalMask: Uint8Array, t: number): boolean {
  const { w, wall } = lv;
  for (const a of [t, t - 1, t - w, t - w - 1]) {
    const b = a + 1;
    const c = a + w;
    const d = c + 1;
    if (!(wall[a] || occupied[a]) || !(wall[b] || occupied[b]) || !(wall[c] || occupied[c]) || !(wall[d] || occupied[d])) continue;
    if ((occupied[a] && !goalMask[a]) || (occupied[b] && !goalMask[b]) || (occupied[c] && !goalMask[c]) || (occupied[d] && !goalMask[d])) return true;
  }
  return false;
}

/**
 * Freeze deadlock: a box is frozen when no push of it is possible (each push's
 * target or pushing square a wall or a frozen box), to a fixpoint. A frozen box
 * off its goal can never move again, so the state is dead. Sound: a box is only
 * called frozen when every one of its pushes is blocked by walls or boxes that
 * are themselves frozen.
 */
function freezeDead(lv: Level, goalMask: Uint8Array, boxes: number[]): boolean {
  const { w, wall } = lv;
  const frozen = new Uint8Array(wall.length);
  let changed = true;
  while (changed) {
    changed = false;
    for (const b of boxes) {
      if (frozen[b]) continue;
      let canMove = false;
      for (const [dx, dy] of DIRS) {
        const d = dy * w + dx;
        const t = b + d;
        const s = b - d;
        if (wall[t] || frozen[t]) continue;
        if (wall[s] || frozen[s]) continue;
        canMove = true;
        break;
      }
      if (!canMove) {
        frozen[b] = 1;
        changed = true;
      }
    }
  }
  return boxes.some((b) => frozen[b] && !goalMask[b]);
}

/** The shortest walk from `from` to `to` around walls and boxes, in lower-case LURD (first direction first on ties). */
function walkTo(lv: Level, occupied: Uint8Array, from: number, to: number): string {
  const { w, wall } = lv;
  if (from === to) return '';
  const prev = new Int32Array(wall.length).fill(-1);
  const how = new Array<string>(wall.length);
  const queue = [from];
  prev[from] = from;
  for (let qi = 0; qi < queue.length; qi++) {
    const p = queue[qi]!;
    if (p === to) break;
    for (const [dx, dy, letter] of DIRS) {
      const q = p + dy * w + dx;
      if (wall[q] || occupied[q] || prev[q] !== -1) continue;
      prev[q] = p;
      how[q] = letter;
      queue.push(q);
    }
  }
  if (prev[to] === -1) throw new Error('walkTo: the push square is out of reach');
  let s = '';
  for (let p = to; p !== from; p = prev[p]!) s = how[p]! + s;
  return s;
}

/** The square the player stands on after `moves` (LURD, case aside) from `from` on a board `w` wide. */
function endOf(w: number, from: number, moves: string): number {
  let p = from;
  for (const ch of moves.toLowerCase()) p += ch === 'u' ? -w : ch === 'd' ? w : ch === 'l' ? -1 : 1;
  return p;
}

interface SearchResult {
  pushes: number;
  moves: string;
  expansions: number;
  states: number;
}

/**
 * A push-optimal search over one board: A* (admissible min-matching heuristic)
 * or plain push-BFS when `mode` is 'bfs'. A state is its boxes and the player's
 * region (named by its lowest square); the first goal state popped is optimal
 * in A* (consistent heuristic), the first generated in BFS. Returns null when
 * the node budget runs out or the board has no solution.
 */
function searchPush(lv: Level, mode: 'astar' | 'bfs', maxStates: number): SearchResult | null {
  const { w, wall, goals, boxes: startBoxes, player: startPlayer } = lv;
  const size = wall.length;
  const n = startBoxes.length;
  const goalMask = new Uint8Array(size);
  for (const g of goals) goalMask[g] = 1;
  const live = liveSquares(lv);
  const wallDead = wallDeadSquares(lv);
  const solved = (bs: readonly number[]): boolean => bs.every((b) => goalMask[b]);
  if (startBoxes.some((b) => !live[b])) return null;
  if (solved(startBoxes)) return { pushes: 0, moves: '', expansions: 0, states: 1 };

  // Walking distance from each goal, and each square's nearest goal.
  const dist = goals.map((g) => bfsDist(lv, g));
  const minDist = new Int32Array(size);
  for (let i = 0; i < size; i++) {
    let m = -1;
    for (const d of dist) {
      if (d[i] >= 0 && (m < 0 || d[i] < m)) m = d[i];
    }
    minDist[i] = m;
  }
  // The heuristic: the cheapest way to match every box to a goal of its own
  // (a push moves one box one step, so this lower-bounds the pushes left).
  // Past six boxes the matching is replaced by the sum of nearest goals,
  // which is still a lower bound.
  const heuristic = (bs: readonly number[]): number => {
    if (n <= 6) {
      let best = Infinity;
      const used = new Array<boolean>(n).fill(false);
      const assign = (i: number, cost: number): void => {
        if (cost >= best) return;
        if (i === bs.length) {
          best = cost;
          return;
        }
        for (let g = 0; g < n; g++) {
          if (used[g]) continue;
          const dd = dist[g]![bs[i]!]!;
          if (dd < 0) continue;
          used[g] = true;
          assign(i + 1, cost + dd);
          used[g] = false;
        }
      };
      assign(0, 0);
      return best;
    }
    let s = 0;
    for (const b of bs) {
      const dd = minDist[b]!;
      if (dd < 0) return Infinity;
      s += dd;
    }
    return s;
  };

  // A state's key: its boxes and its region's lowest square. Numeric while
  // size ** (boxes + 1) stays under 2 ** 53, a string past that.
  const numericKey = Math.pow(size, n + 1) < 2 ** 53;
  const keyOf = (bs: readonly number[], low: number): number | string => {
    if (numericKey) {
      let k = low;
      for (const b of bs) k = k * size + b;
      return k;
    }
    return `${low}:${bs.join(',')}`;
  };

  const sBoxes: number[][] = [startBoxes.slice()];
  const sPlayer: number[] = [startPlayer];
  const sLow: number[] = [0];
  const sParent: number[] = [-1];
  const sFrom: number[] = [-1];
  const sTo: number[] = [-1];
  const sG: number[] = [0];
  const best = new Map<number | string, number>();
  const occupied = new Uint8Array(size);
  const seen = new Int32Array(size);
  const mark = new Int32Array(size);
  const stack = new Int32Array(size);
  let stamp = 0;
  for (const b of startBoxes) occupied[b] = 1;
  sLow[0] = reach(lv, occupied, startPlayer, seen, ++stamp, stack);
  for (const b of startBoxes) occupied[b] = 0;
  best.set(keyOf(startBoxes, sLow[0]!), 0);

  // The open list, a heap on (f, -g, index): lowest f first, deeper first on
  // ties, earliest first past that. Deterministic throughout.
  const heap: [number, number, number][] = [];
  const less = (a: [number, number, number], b: [number, number, number]): boolean =>
    a[0] < b[0] || (a[0] === b[0] && (a[1] > b[1] || (a[1] === b[1] && a[2] < b[2])));
  const heapPush = (e: [number, number, number]): void => {
    let i = heap.length;
    heap.push(e);
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!less(heap[i]!, heap[p]!)) break;
      [heap[i], heap[p]] = [heap[p]!, heap[i]!];
      i = p;
    }
  };
  const heapPop = (): [number, number, number] => {
    const top = heap[0]!;
    const last = heap.pop()!;
    if (heap.length > 0) {
      heap[0] = last;
      for (let i = 0; ; ) {
        let c = 2 * i + 1;
        if (c >= heap.length) break;
        if (c + 1 < heap.length && less(heap[c + 1]!, heap[c]!)) c++;
        if (!less(heap[c]!, heap[i]!)) break;
        [heap[i], heap[c]] = [heap[c]!, heap[i]!];
        i = c;
      }
    }
    return top;
  };
  heapPush([mode === 'astar' ? heuristic(startBoxes) : 0, 0, 0]);

  let expansions = 0;
  let found = -1;
  while (heap.length > 0) {
    const [, g, s] = heapPop();
    const bs = sBoxes[s]!;
    if (best.get(keyOf(bs, sLow[s]!)) !== g) continue; // a stale entry
    if (solved(bs)) {
      found = s;
      break;
    }
    if (expansions >= maxStates) return null;
    expansions++;
    for (const b of bs) occupied[b] = 1;
    reach(lv, occupied, sPlayer[s]!, seen, ++stamp, stack);
    const here = stamp;
    for (let bi = 0; bi < n && found < 0; bi++) {
      const b = bs[bi]!;
      for (const [dx, dy, , up] of DIRS) {
        const d = dy * w + dx;
        const t = b + d;
        if (wall[t] || occupied[t] || !live[t] || wallDead[t]) continue;
        if (seen[b - d] !== here) continue; // the player cannot reach the push square
        const next = bs.slice();
        next[bi] = t;
        next.sort((a, b2) => a - b2);
        occupied[b] = 0;
        occupied[t] = 1;
        const dead = frozenBlock(lv, occupied, goalMask, t) || freezeDead(lv, goalMask, next);
        let key: number | string = '';
        let low = 0;
        if (!dead) {
          low = reach(lv, occupied, b, mark, ++stamp, stack);
          key = keyOf(next, low);
        }
        occupied[t] = 0;
        occupied[b] = 1;
        if (dead) continue;
        const ng = g + 1;
        const known = best.get(key);
        if (known !== undefined && known <= ng) continue;
        best.set(key, ng);
        const idx = sBoxes.length;
        sBoxes.push(next);
        sPlayer.push(b);
        sLow.push(low);
        sParent.push(s);
        sFrom.push(b);
        sTo.push(t);
        sG.push(ng);
        heapPush([mode === 'astar' ? ng + heuristic(next) : ng, ng, idx]);
        // In BFS the first goal state generated is optimal; in A* it is the
        // first goal state popped, so only BFS may stop here.
        if (mode === 'bfs' && solved(next)) {
          found = idx;
          break;
        }
      }
    }
    for (const b of bs) occupied[b] = 0;
  }
  if (found < 0) return null;
  // The push path, then the moves: walk to each push's square, then push.
  const path: number[] = [];
  for (let s = found; s > 0; s = sParent[s]!) path.push(s);
  path.reverse();
  let moves = '';
  let player = startPlayer;
  let boxes = startBoxes.slice();
  for (const s of path) {
    const from = sFrom[s]!;
    const to = sTo[s]!;
    const d = to - from;
    for (const b of boxes) occupied[b] = 1;
    moves += walkTo(lv, occupied, player, from - d);
    for (const b of boxes) occupied[b] = 0;
    moves += DIRS.find(([dx, dy]) => dy * w + dx === d)![3];
    player = from;
    boxes = boxes.map((b) => (b === from ? to : b)).sort((a, b2) => a - b2);
  }
  return { pushes: path.length, moves, expansions, states: sBoxes.length };
}

interface Room {
  squares: number[];
  boxes: number[];
  goals: number[];
  done: boolean;
}

/**
 * The level's rooms: cut the dead squares of the player's row (the hallway: a
 * box there reaches no goal) out of the floor, and each part left holding boxes
 * is a room. Null when a box starts in the hallway, a goal is cut off, or some
 * part holds more boxes than goals: then the level is no set of rooms.
 */
function roomsOf(lv: Level): Room[] | null {
  const { w, wall, goals, boxes, player } = lv;
  const live = liveSquares(lv);
  const row = Math.floor(player / w);
  const cut = new Uint8Array(wall.length);
  for (let i = row * w; i < (row + 1) * w; i++) if (!wall[i] && !live[i]) cut[i] = 1;
  if (boxes.some((b) => cut[b])) return null;
  const part = new Int32Array(wall.length).fill(-1);
  const rooms: Room[] = [];
  for (let s = 0; s < wall.length; s++) {
    if (wall[s] || cut[s] || part[s] >= 0) continue;
    const squares = [s];
    part[s] = rooms.length;
    for (let i = 0; i < squares.length; i++) {
      for (const [dx, dy] of DIRS) {
        const q = squares[i]! + dy * w + dx;
        if (!wall[q] && !cut[q] && part[q] < 0) {
          part[q] = rooms.length;
          squares.push(q);
        }
      }
    }
    rooms.push({ squares, boxes: [], goals: [], done: false });
  }
  for (const b of boxes) rooms[part[b]!]!.boxes.push(b);
  for (const g of goals) {
    if (part[g]! < 0) return null;
    rooms[part[g]!]!.goals.push(g);
  }
  if (rooms.some((r) => r.boxes.length !== r.goals.length)) return null;
  return rooms.filter((r) => r.boxes.length > 0);
}

/**
 * The level solved room by room: each room's push-optimal solution in turn, the
 * other rooms' boxes standing as walls (on their goals once their room is done),
 * the player walking on from where the last room left it. A box never leaves its
 * room, so the rooms' optima add up to the level's.
 */
function solveByRooms(lv: Level): SearchResult | null {
  const rooms = roomsOf(lv);
  if (rooms === null) return null;
  let player = lv.player;
  let pushes = 0;
  let moves = '';
  let expansions = 0;
  let states = 0;
  for (const room of rooms) {
    const wall = lv.wall.slice();
    for (const other of rooms) {
      if (other === room) continue;
      for (const b of other.done ? other.goals : other.boxes) wall[b] = 1;
    }
    const sub: Level = {
      w: lv.w,
      h: lv.h,
      wall,
      goals: room.goals.slice().sort((a, b) => a - b),
      boxes: room.boxes.slice().sort((a, b) => a - b),
      player,
    };
    let solved = searchPush(sub, 'astar', ASTAR_EXPANSIONS);
    if (solved === null) solved = searchPush(sub, 'bfs', BFS_STATES);
    if (solved === null) return null;
    pushes += solved.pushes;
    moves += solved.moves;
    expansions += solved.expansions;
    states += solved.states;
    player = endOf(lv.w, player, solved.moves);
    room.done = true;
  }
  return { pushes, moves, expansions, states };
}

/** Solve one level: room by room first, the whole level as a last resort. */
function solveLevel(text: string): string {
  const lv = parseLevel(text);
  const byRooms = solveByRooms(lv);
  if (byRooms !== null) return byRooms.moves;
  const whole = searchPush(lv, 'astar', WHOLE_LEVEL_EXPANSIONS);
  if (whole !== null) return whole.moves;
  return '';
}

for (const id of readdirSync(INPUT_DIR).sort()) {
  let moves = '';
  try {
    moves = solveLevel(readFileSync(join(INPUT_DIR, id, 'level.txt'), 'utf8'));
  } catch {
    moves = '';
  }
  mkdirSync(join(OUTPUT_DIR, id), { recursive: true });
  writeFileSync(join(OUTPUT_DIR, id, 'solution.txt'), `${moves}\n`);
}
