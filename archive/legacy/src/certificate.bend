import Base
import ./rules.bend as Rules
import ./pawn.bend as Pawn

# A certificate is a rank on winning positions. Ranks strictly decrease along
# the winning side's chosen move and along every reply by the defending side.
# Zero denotes a drawing or invalid position.
type Scan is Type:
  Scan{table: Array<U32>, moves: U32, lower: Bool,
    won: Bool, all_lower: Bool, draw: Bool}

def scan.new(table: Array<U32>) -> Scan:
  Scan{table, 0, False{}, False{}, True{}, False{}}

def scan.read(+rank: U32, moves: U32, lower: Bool,
  won: Bool, all_lower: Bool, draw: Bool,
  read: Array<U32> & U32) -> Scan:
  match read:
    case (table, +value):
      Scan{table, (moves + 1 : U32),
        lower || (U32.is_ne(value, 0) && U32.is_lt(value, rank)),
        won || U32.is_ne(value, 0),
        all_lower && U32.is_ne(value, 0) && U32.is_lt(value, rank),
        draw || U32.is_eq(value, 0)}

def scan.edge(scan: Scan, rank: U32, i: U32) -> Scan:
  match scan:
    case Scan{table, moves, lower, won, all_lower, draw}:
      scan.read(rank, moves, lower, won, all_lower, draw, table[i])

def scan.capture(scan: Scan) -> Scan:
  match scan:
    case Scan{table, moves, lower, won, all_lower, draw}:
      Scan{table, (moves + 1 : U32), lower, won, False{}, True{}}

def scan.legal(scan: Scan, rank: U32, i: U32,
  legal: Bool) -> Scan:
  match legal:
    case False{}:
      scan
    case True{}:
      scan.edge(scan, rank, i)

def white_king.go(fuel: Nat, +kind: U32, +s: Rules.State,
  +wk: U32, +bk: U32, +pc: U32, +dest: U32,
  +rank: U32, scan: Scan) -> Scan:
  match fuel:
    case 0n:
      scan
    case 1n+rest:
      +next = {Rules.State{dest, bk, pc, 1} : Rules.State}
      scan = scan.legal(scan, rank, Rules.index(next),
        Rules.move_to(kind, s, next))
      white_king.go(rest, kind, s, wk, bk, pc,
        (dest + 1 : U32), rank, scan)

def white_piece.go(fuel: Nat, +kind: U32, +s: Rules.State,
  +wk: U32, +bk: U32, +pc: U32, +dest: U32,
  +rank: U32, scan: Scan) -> Scan:
  match fuel:
    case 0n:
      scan
    case 1n+rest:
      +next = {Rules.State{wk, bk, dest, 1} : Rules.State}
      scan = scan.legal(scan, rank, Rules.index(next),
        Rules.move_to(kind, s, next))
      white_piece.go(rest, kind, s, wk, bk, pc,
        (dest + 1 : U32), rank, scan)

def black.capture(scan: Scan, rank: U32, i: U32,
  capture: Bool) -> Scan:
  match capture:
    case True{}:
      scan.capture(scan)
    case False{}:
      scan.edge(scan, rank, i)

def black.capture_or_move(scan: Scan, rank: U32, i: U32,
  legal: Bool, capture: Bool) -> Scan:
  match legal:
    case False{}:
      scan
    case True{}:
      black.capture(scan, rank, i, capture)

def black.consider(scan: Scan, +kind: U32,
  +next: Rules.State, +wk: U32, +bk: U32, +pc: U32,
  +dest: U32, rank: U32) -> Scan:
  black.capture_or_move(scan, rank, Rules.index(next),
    Rules.black_move(kind, wk, bk, pc, dest),
    U32.is_eq(dest, pc))

def black.go(fuel: Nat, +kind: U32,
  +wk: U32, +bk: U32, +pc: U32, +dest: U32,
  +rank: U32, scan: Scan) -> Scan:
  match fuel:
    case 0n:
      scan
    case 1n+rest:
      next = {Rules.State{wk, dest, pc, 0} : Rules.State}
      scan = black.consider(scan, kind, next, wk, bk, pc,
        dest, rank)
      black.go(rest, kind, wk, bk, pc,
        (dest + 1 : U32), rank, scan)

def moves(table: Array<U32>, +kind: U32,
  s: Rules.State, +rank: U32) -> Scan:
  match s:
    case Rules.State{+wk, +bk, +pc, 0}:
      +s = {Rules.State{wk, bk, pc, 0} : Rules.State}
      scan = white_king.go(64n, kind, s, wk, bk, pc, 0,
        rank, scan.new(table))
      white_piece.go(64n, kind, s, wk, bk, pc, 0, rank, scan)
    case Rules.State{+wk, +bk, +pc, 1}:
      black.go(64n, kind, wk, bk, pc, 0, rank, scan.new(table))
    case _:
      scan.new(table)

def evaluate.white(rank: U32, +promotion: Bool, scan: Scan) ->
  Array<U32> & Bool:
  match scan:
    case Scan{table, moves, lower, won, all_lower, draw}:
      (table, Bool.pick(Bool, U32.is_eq(rank, 0),
        Bool.not(won || promotion), lower || promotion))

def black_in_check(kind: U32, s: Rules.State) -> Bool:
  match s:
    case Rules.State{wk, bk, pc, turn}:
      Rules.attacks(kind, pc, bk, wk)

def evaluate.black(+kind: U32, +s: Rules.State,
  +rank: U32, scan: Scan) -> Array<U32> & Bool:
  match scan:
    case Scan{table, +moves, lower, won, all_lower, draw}:
      +mate = U32.is_eq(moves, 0) && black_in_check(kind, s)
      (table, Bool.pick(Bool, U32.is_eq(rank, 0),
        draw || (U32.is_eq(moves, 0) && Bool.not(mate)),
        (U32.is_ne(moves, 0) && all_lower) ||
        (U32.is_eq(rank, 1) && mate)))

def evaluate(+kind: U32, +s: Rules.State, rank: U32,
  promotion: Bool, scan: Scan) -> Array<U32> & Bool:
  match s:
    case Rules.State{wk, bk, pc, 0}:
      evaluate.white(rank, promotion, scan)
    case Rules.State{wk, bk, pc, 1}:
      evaluate.black(kind, Rules.State{wk, bk, pc, 1}, rank, scan)
    case _:
      evaluate.white(rank, promotion, scan)

# A clock-0 win certified by at most 49 same-class plies, or 49 pawn plies
# followed by at most 49 promoted-piece plies, finishes before the terminal
# 100-halfmove draw. This is a conservative bound, not a DTM value.
def entry.bound(+rank: U32,
  checked: Array<U32> & Bool) -> Array<U32> & Bool:
  match checked:
    case (table, okay):
      (table, okay && U32.is_le(rank, 49))

def entry.valid(+kind: U32, +s: Rules.State,
  +rank: U32, promotion: Bool, table: Array<U32>) ->
  Array<U32> & Bool:
  entry.bound(rank,
    evaluate(kind, s, rank, promotion, moves(table, kind, s, rank)))

def entry.if(+kind: U32, +s: Rules.State,
  rank: U32, promotion: Bool, table: Array<U32>,
  valid: Bool) -> Array<U32> & Bool:
  match valid:
    case False{}:
      (table, U32.is_eq(rank, 0))
    case True{}:
      entry.valid(kind, s, rank, promotion, table)

def entry.read(+kind: U32, +s: Rules.State,
  promotion: Bool, read: Array<U32> & U32) ->
  Array<U32> & Bool:
  match read:
    case (table, rank):
      entry.if(kind, s, rank, promotion, table, Rules.valid(kind, s))

def entry(table: Array<U32>, +kind: U32, +i: U32,
  promotion: Bool) -> Array<U32> & Bool:
  +s = Rules.decode(i)
  entry.read(kind, s, promotion, table[i])

type Check is Type:
  Check{table: Array<U32>, okay: Bool}

def check.step.read(prior: Bool, read: Array<U32> & Bool) -> Check:
  match read:
    case (table, okay):
      Check{table, prior && okay}

def check.step(check: Check, +kind: U32, i: U32) -> Check:
  match check:
    case Check{table, okay}:
      check.step.read(okay, entry(table, kind, i, False{}))

def check.go(fuel: Nat, +kind: U32, +i: U32,
  check: Check) -> Check:
  match fuel:
    case 0n:
      check
    case 1n+rest:
      check.go(rest, kind, (i + 1 : U32), check.step(check, kind, i))

def check(table: Array<U32>, kind: U32) -> Check:
  check.go(524288n, kind, 0, Check{table, True{}})

type PawnCheck is Type:
  PawnCheck{promoted: Pawn.Promoted, table: Array<U32>, okay: Bool}

def pawn.step.finish(prior: Bool, promoted: Pawn.Promoted,
  read: Array<U32> & Bool) -> PawnCheck:
  match read:
    case (table, okay):
      PawnCheck{promoted, table, prior && okay}

def pawn.step.promotion(prior: Bool, table: Array<U32>,
  i: U32, read: Pawn.Promoted & Bool) -> PawnCheck:
  match read:
    case (promoted, wins):
      pawn.step.finish(prior, promoted, entry(table, 4, i, wins))

def pawn.step.if(prior: Bool, promoted: Pawn.Promoted,
  table: Array<U32>, i: U32, target_i: U32,
  can_promote: Bool) -> PawnCheck:
  match can_promote:
    case True{}:
      pawn.step.promotion(prior, table, i,
        Pawn.promotion_wins(promoted, target_i))
    case False{}:
      pawn.step.finish(prior, promoted, entry(table, 4, i, False{}))

def pawn.step.state(prior: Bool, promoted: Pawn.Promoted,
  table: Array<U32>, +i: U32, s: Rules.State) -> PawnCheck:
  match s:
    case Rules.State{+wk, +bk, +pc, 0}:
      +target = (pc + 8 : U32)
      can_promote = Rules.pawn_can_promote(wk, bk, pc)
      target_i = Rules.index(Rules.State{wk, bk, target, 1})
      pawn.step.if(prior, promoted, table, i, target_i, can_promote)
    case _:
      pawn.step.finish(prior, promoted, entry(table, 4, i, False{}))

def pawn.step(pawn: PawnCheck, +i: U32) -> PawnCheck:
  match pawn:
    case PawnCheck{promoted, table, okay}:
      pawn.step.state(okay, promoted, table, i, Rules.decode(i))

def pawn.go(fuel: Nat, +i: U32, pawn: PawnCheck) -> PawnCheck:
  match fuel:
    case 0n:
      pawn
    case 1n+rest:
      pawn.go(rest, (i + 1 : U32), pawn.step(pawn, i))

def check_pawn(promoted: Pawn.Promoted,
  table: Array<U32>) -> PawnCheck:
  pawn.go(524288n, 0, PawnCheck{promoted, table, True{}})

def piece.knight(queen: Array<U32>, rook: Array<U32>,
  bishop: Array<U32>, prior: Bool,
  checked: Check) -> Pawn.Promoted & Bool:
  match checked:
    case Check{table, okay}:
      (Pawn.Promoted{queen, rook, bishop, table}, prior && okay)

def piece.bishop(queen: Array<U32>, rook: Array<U32>,
  knight: Array<U32>, prior: Bool,
  checked: Check) -> Pawn.Promoted & Bool:
  match checked:
    case Check{table, okay}:
      piece.knight(queen, rook, table, prior && okay, check(knight, 3))

def piece.rook(queen: Array<U32>, bishop: Array<U32>,
  knight: Array<U32>, prior: Bool,
  checked: Check) -> Pawn.Promoted & Bool:
  match checked:
    case Check{table, okay}:
      piece.bishop(queen, table, knight, prior && okay, check(bishop, 2))

def piece.queen(rook: Array<U32>, bishop: Array<U32>,
  knight: Array<U32>, checked: Check) -> Pawn.Promoted & Bool:
  match checked:
    case Check{table, okay}:
      piece.rook(table, bishop, knight, okay, check(rook, 1))

def check_pieces(promoted: Pawn.Promoted) -> Pawn.Promoted & Bool:
  match promoted:
    case Pawn.Promoted{queen, rook, bishop, knight}:
      piece.queen(rook, bishop, knight, check(queen, 0))

def all.pawn_checked(prior: Bool, pawn: PawnCheck) ->
  (Pawn.Promoted & Array<U32>) & Bool:
  match pawn:
    case PawnCheck{promoted, table, okay}:
      ((promoted, table), prior && okay)

def all.pieces(pawn: Array<U32>, checked: Pawn.Promoted & Bool) ->
  (Pawn.Promoted & Array<U32>) & Bool:
  match checked:
    case (promoted, okay):
      all.pawn_checked(okay, check_pawn(promoted, pawn))

def all(pair: Pawn.Promoted & Array<U32>) ->
  (Pawn.Promoted & Array<U32>) & Bool:
  match pair:
    case (promoted, pawn):
      all.pieces(pawn, check_pieces(promoted))
