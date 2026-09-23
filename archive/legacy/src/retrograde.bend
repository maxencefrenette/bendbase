import Base
import ./rules.bend as Rules
import ./proof_tree.bend as ProofTree
import ./proof_queue.bend as ProofQueue
import ./squares.bend as Squares

# The queue holds each newly proven white win exactly once. A black position is
# proven lost when every legal move has reached a proven white win. Moves that
# capture the extra piece lead to K vs K and therefore never enter the queue.
type Work is Data:
  Work{won: ProofTree.Tree, queue: ProofQueue.Queue,
    squares: List<&2, U32>}

def new() -> Work:
  Work{ProofTree.filled(19n, 0), ProofQueue.new(),
    Squares.all6()}

def marked(work: Work, i: U32) -> Work & U32:
  match work:
    case Work{+won, queue, squares}:
      (Work{won, queue, squares},
        ProofTree.get_index(won, i))

def mark.new(work: Work, +state: Rules.State, rank: U32) -> Work:
  match work:
    case Work{won, queue, squares}:
      won = ProofTree.set_index(won, Rules.index(state), rank)
      queue = ProofQueue.push(queue, state)
      Work{won, queue, squares}

def mark.if_decision(work: Work, state: Rules.State,
  rank: U32, zero: Bool) -> Work:
  match zero:
    case True{}:
      mark.new(work, state, rank)
    case False{}:
      work

def mark.if(work: Work, state: Rules.State,
  rank: U32, old: U32) -> Work:
  mark.if_decision(work, state, rank, U32.is_eq(old, 0))

def mark.read(state: Rules.State, rank: U32,
  read: Work & U32) -> Work:
  match read:
    case (work, old):
      mark.if(work, state, rank, old)

def mark.rank(work: Work, +state: Rules.State, rank: U32) -> Work:
  mark.read(state, rank, marked(work, Rules.index(state)))

def mark(work: Work, +state: Rules.State) -> Work:
  mark.rank(work, state, 1)

def black_has_move.go(fuel: Nat, +kind: U32, +wk: U32,
  +bk: U32, +pc: U32, +dest: U32,
  found: Bool) -> Bool:
  match fuel:
    case 0n:
      found
    case 1n+rest:
      black_has_move.go(rest, kind, wk, bk, pc,
        (dest + 1 : U32),
        found || Rules.black_move(kind, wk, bk, pc, dest))

def black_has_move.squares(+kind: U32, +wk: U32,
  +bk: U32, +pc: U32, squares: List<&2, U32>,
  found: Bool) -> Bool:
  match squares:
    case Nil{}:
      found
    case dest <> rest:
      black_has_move.squares(kind, wk, bk, pc,
        rest, found || Rules.black_move(kind, wk, bk, pc, dest))

def black_has_move(kind: U32, s: Rules.State,
  squares: List<&2, U32>) -> Bool:
  match s:
    case Rules.State{wk, bk, pc, turn}:
      black_has_move.squares(kind, wk, bk, pc,
        squares, False{})

def init_state.mate(work: Work, state: Rules.State,
  mate: Bool) -> Work:
  match mate:
    case True{}:
      mark(work, state)
    case False{}:
      work

def init_state.black(work: Work, +kind: U32, +i: U32,
  +wk: U32, +bk: U32, +pc: U32) -> Work:
  match work:
    case Work{won, queue, +squares}:
      mate = Bool.not(black_has_move(kind,
        Rules.State{wk, bk, pc, 1}, squares)) &&
        Rules.attacks(kind, pc, bk, wk)
      init_state.mate(Work{won, queue, squares},
        Rules.State{wk, bk, pc, 1}, mate)

def init_state.black.if(work: Work, +kind: U32,
  +i: U32, +wk: U32, +bk: U32, +pc: U32,
  black: Bool) -> Work:
  match black:
    case True{}:
      init_state.black(work, kind, i, wk, bk, pc)
    case False{}:
      work

def init_state.valid(work: Work, +kind: U32, +i: U32,
  s: Rules.State) -> Work:
  match s:
    case Rules.State{wk, bk, pc, turn}:
      init_state.black.if(work, kind, i, wk, bk,
        pc, U32.is_eq(turn, 1))

def init_state.if(work: Work, kind: U32, i: U32,
  s: Rules.State, valid: Bool) -> Work:
  match valid:
    case True{}:
      init_state.valid(work, kind, i, s)
    case False{}:
      work

def init_state(work: Work, +kind: U32, +i: U32) -> Work:
  +s = Rules.decode(i)
  init_state.if(work, kind, i, s, Rules.valid(kind, s))

def init.go(fuel: Nat, +kind: U32, +i: U32, work: Work) -> Work:
  match fuel:
    case 0n:
      work
    case 1n+rest:
      init.go(rest, kind, (i + 1 : U32), init_state(work, kind, i))

def init(kind: U32) -> Work:
  init.go(524288n, kind, 0, new())

# Rechecking Black's replies removes the mutable-counter invariant. A Black
# state is marked only when it has at least one legal reply and every reply is
# an already marked White win. Capturing the extra piece is a permanent draw
# exit and therefore prevents readiness. The assigned rank is one more than
# the maximum reply rank, independently of queue processing order.
type BlackReplyScan is Data:
  BlackReplyScan{seen: Bool, all_won: Bool, maximum: U32}

def black_reply_consider(scan: BlackReplyScan, +rank: U32,
  capture: Bool, legal: Bool) -> BlackReplyScan:
  match scan:
    case BlackReplyScan{seen, all_won, maximum}:
      match legal:
        case False{}:
          BlackReplyScan{seen, all_won, maximum}
        case True{}:
          BlackReplyScan{True{},
            all_won && Bool.not(capture) && U32.is_ne(rank, 0),
            U32.max(maximum, rank)}

def black_reply_scan.go(fuel: Nat, +kind: U32, +wk: U32,
  +bk: U32, +pc: U32, +dest: U32, +won: ProofTree.Tree,
  scan: BlackReplyScan) -> BlackReplyScan:
  match fuel:
    case 0n:
      scan
    case 1n+rest:
      +next = {Rules.State{wk, dest, pc, 0} : Rules.State}
      rank = ProofTree.get_index(won, Rules.index(next))
      scan = black_reply_consider(scan, rank,
        U32.is_eq(dest, pc),
        Rules.black_move(kind, wk, bk, pc, dest))
      black_reply_scan.go(rest, kind, wk, bk, pc,
        (dest + 1 : U32), won, scan)

def black_reply_scan.squares(+kind: U32, +wk: U32,
  +bk: U32, +pc: U32, squares: List<&2, U32>,
  +won: ProofTree.Tree,
  scan: BlackReplyScan) -> BlackReplyScan:
  match squares:
    case Nil{}:
      scan
    case +dest <> rest:
      +next = {Rules.State{wk, dest, pc, 0} : Rules.State}
      rank = ProofTree.get_index(won, Rules.index(next))
      scan = black_reply_consider(scan, rank,
        U32.is_eq(dest, pc),
        Rules.black_move(kind, wk, bk, pc, dest))
      black_reply_scan.squares(kind, wk, bk, pc,
        rest, won, scan)

def black_reply_scan(kind: U32, s: Rules.State,
  won: ProofTree.Tree,
  squares: List<&2, U32>) -> BlackReplyScan:
  match s:
    case Rules.State{wk, bk, pc, turn}:
      black_reply_scan.squares(kind, wk, bk, pc,
        squares, won,
        BlackReplyScan{False{}, True{}, 0})

def black_ready.if(work: Work, state: Rules.State,
  maximum: U32, ready: Bool) -> Work:
  match ready:
    case True{}:
      mark.rank(work, state, (maximum + 1 : U32))
    case False{}:
      work

def black_ready.fin(work: Work, state: Rules.State,
  scan: BlackReplyScan) -> Work:
  match scan:
    case BlackReplyScan{seen, all_won, maximum}:
      black_ready.if(work, state, maximum,
        seen && all_won)

def black_ready(work: Work, +kind: U32,
  +state: Rules.State) -> Work:
  match work:
    case Work{+won, queue, +squares}:
      black_ready.fin(Work{won, queue, squares},
        state, black_reply_scan(kind, state, won,
          squares))

def predecessor.update.turn.decide(work: Work, kind: U32,
  state: Rules.State, rank: U32,
  white: Bool) -> Work:
  match white:
    case True{}:
      mark.rank(work, state, rank)
    case False{}:
      black_ready(work, kind, state)

def predecessor.update.turn(work: Work, kind: U32,
  state: Rules.State, turn: U32,
  rank: U32) -> Work:
  predecessor.update.turn.decide(work, kind,
    state, rank, U32.is_eq(turn, 0))

def predecessor.update.if(work: Work, kind: U32,
  state: Rules.State,
  turn: U32, rank: U32,
  legal: Bool) -> Work:
  match legal:
    case False{}:
      work
    case True{}:
      predecessor.update.turn(work, kind, state, turn, rank)

def predecessor.update(work: Work, +kind: U32,
  +previous: Rules.State, +current: Rules.State, turn: U32,
  rank: U32) -> Work:
  predecessor.update.if(work, kind, previous, turn, rank,
    Rules.move_to(kind, previous, current))

def previous_king.go(squares: List<&2, U32>,
  +kind: U32, +current: Rules.State,
  +wk: U32, +bk: U32, +pc: U32,
  +rank: U32, work: Work) -> Work:
  match squares:
    case Nil{}:
      work
    case src <> rest:
      next = predecessor.update(work, kind,
        Rules.State{src, bk, pc, 0}, current, 0, rank)
      previous_king.go(rest, kind, current, wk, bk, pc,
        rank, next)

def previous_piece.go(squares: List<&2, U32>,
  +kind: U32, +current: Rules.State,
  +wk: U32, +bk: U32, +pc: U32,
  +rank: U32, work: Work) -> Work:
  match squares:
    case Nil{}:
      work
    case src <> rest:
      next = predecessor.update(work, kind,
        Rules.State{wk, bk, src, 0}, current, 0, rank)
      previous_piece.go(rest, kind, current, wk, bk, pc,
        rank, next)

def previous_black.go(squares: List<&2, U32>,
  +kind: U32, +current: Rules.State,
  +wk: U32, +bk: U32, +pc: U32,
  +rank: U32, work: Work) -> Work:
  match squares:
    case Nil{}:
      work
    case src <> rest:
      next = predecessor.update(work, kind,
        Rules.State{wk, src, pc, 1}, current, 1, rank)
      previous_black.go(rest, kind, current, wk, bk, pc,
        rank, next)

def predecessors.choose(work: Work,
  +squares: List<&2, U32>, +kind: U32,
  +wk: U32, +bk: U32, +pc: U32,
  +rank: U32, white: Bool, black: Bool) -> Work:
  match white:
    case True{}:
      previous_black.go(squares, kind,
        Rules.State{wk, bk, pc, 0},
        wk, bk, pc, rank, work)
    case False{}:
      match black:
        case True{}:
          +current = {Rules.State{wk, bk, pc, 1} : Rules.State}
          work = previous_king.go(squares, kind,
            current, wk, bk, pc, rank, work)
          previous_piece.go(squares, kind, current,
            wk, bk, pc, rank, work)
        case False{}:
          work

def predecessors(work: Work, +kind: U32, current: Rules.State,
  +rank: U32) -> Work:
  match work:
    case Work{won, queue, +squares}:
      match current:
        case Rules.State{wk, bk, pc, +turn}:
          predecessors.choose(Work{won, queue, squares},
            squares, kind, wk, bk, pc, rank,
            U32.is_eq(turn, 0), U32.is_eq(turn, 1))

def take.fin(won: ProofTree.Tree,
  squares: List<&2, U32>,
  read: ProofQueue.Queue & Maybe<&2, Rules.State>) ->
  Work & Maybe<&2, Rules.State>:
  match read:
    case (queue, state):
      (Work{won, queue, squares}, state)

def take(work: Work) -> Work & Maybe<&2, Rules.State>:
  match work:
    case Work{won, queue, squares}:
      take.fin(won, squares, ProofQueue.pop(queue))

def propagate.rank(kind: U32, state: Rules.State,
  read: Work & U32) -> Work:
  match read:
    case (work, rank):
      predecessors(work, kind, state, (rank + 1 : U32))

def propagate.consume(kind: U32,
  read: Work & Maybe<&2, Rules.State>) -> Work:
  match read:
    case (work, None{}):
      work
    case (work, Some{+state}):
      propagate.rank(kind, state,
        marked(work, Rules.index(state)))

def propagate.step(kind: U32, work: Work) -> Work:
  propagate.consume(kind, take(work))

def propagate.go(fuel: Nat, +kind: U32, work: Work) -> Work:
  match fuel:
    case 0n:
      work
    case 1n+rest:
      propagate.go(rest, kind, propagate.step(kind, work))

def solve.fin(work: Work) -> Array<U32>:
  match work:
    case Work{won, queue, squares}:
      ProofTree.to_array(won)

def solve.work(init_fuel: Nat, propagate_fuel: Nat,
  +kind: U32) -> Work:
  propagate.go(propagate_fuel, kind,
    init.go(init_fuel, kind, 0, new()))

def solve(+kind: U32) -> Array<U32>:
  solve.fin(solve.work(524288n, 524288n, kind))
