import Base
import ./rules.bend as Rules
import ./wdl_spec.bend as WDL
import ./proof_tree.bend as ProofTree
import ./retrograde.bend as Retro

# One Bellman step at a fixed halfmove clock. `next` contains values after a
# nonzeroing move; `reset` contains pawn values at clock zero after a push.
# Queen and rook tables are already solved at clock zero for promotions.
def white_king.go(squares: List<&2, U32>, +kind: U32,
  +state: Rules.State, +wk: U32, +bk: U32, +pc: U32,
  +next: ProofTree.Tree) -> Bool:
  match squares:
    case Nil{}:
      False{}
    case dest <> rest:
      +target = {Rules.State{dest, bk, pc, 1} : Rules.State}
      (Rules.move_to(kind, state, target) &&
        U32.is_ne(ProofTree.get_index(next,
          Rules.index(target)), 0)) ||
      white_king.go(rest, kind, state, wk, bk, pc, next)

def white_piece.value(+kind: U32, +pc: U32,
  +dest: U32, +target: Rules.State,
  +next: ProofTree.Tree, +reset: ProofTree.Tree) -> U32:
  Bool.pick(U32,
    U32.is_eq(kind, 4) && U32.is_ne(pc, dest),
    ProofTree.get_index(reset, Rules.index(target)),
    ProofTree.get_index(next, Rules.index(target)))

def white_piece.go(squares: List<&2, U32>, +kind: U32,
  +state: Rules.State, +wk: U32, +bk: U32, +pc: U32,
  +next: ProofTree.Tree, +reset: ProofTree.Tree) -> Bool:
  match squares:
    case Nil{}:
      False{}
    case +dest <> rest:
      +target = {Rules.State{wk, bk, dest, 1} : Rules.State}
      (Rules.move_to(kind, state, target) &&
        U32.is_ne(white_piece.value(kind, pc, dest,
          target, next, reset), 0)) ||
      white_piece.go(rest, kind, state, wk, bk, pc,
        next, reset)

def white_promotion(+wk: U32, +bk: U32, +pc: U32,
  +queen: ProofTree.Tree, +rook: ProofTree.Tree) -> Bool:
  +target = (pc + 8 : U32)
  +index = Rules.index(Rules.State{wk, bk, target, 1})
  (WDL.promotion(wk, bk, pc, 0, wk, bk, target) &&
    U32.is_ne(ProofTree.get_index(queen, index), 0)) ||
  (WDL.promotion(wk, bk, pc, 1, wk, bk, target) &&
    U32.is_ne(ProofTree.get_index(rook, index), 0))

def white_value(+kind: U32, +wk: U32, +bk: U32,
  +pc: U32, +squares: List<&2, U32>,
  +next: ProofTree.Tree, +reset: ProofTree.Tree,
  +queen: ProofTree.Tree, +rook: ProofTree.Tree) -> Bool:
  +state = {Rules.State{wk, bk, pc, 0} : Rules.State}
  white_king.go(squares, kind, state, wk, bk, pc,
    next) ||
  white_piece.go(squares, kind, state, wk, bk, pc,
    next, reset) ||
  (U32.is_eq(kind, 4) &&
    white_promotion(wk, bk, pc, queen, rook))

def black_value.fin(+kind: U32, +wk: U32,
  +bk: U32, +pc: U32,
  scan: Retro.BlackReplyScan) -> Bool:
  match scan:
    case Retro.BlackReplyScan{+seen, all_won, maximum}:
      (Bool.not(seen) && Rules.attacks(kind, pc, bk, wk)) ||
      (seen && all_won)

def black_value(+kind: U32, +wk: U32, +bk: U32,
  +pc: U32, +squares: List<&2, U32>,
  +next: ProofTree.Tree) -> Bool:
  black_value.fin(kind, wk, bk, pc,
    Retro.black_reply_scan.squares(kind, wk, bk,
      pc, squares, next,
      Retro.BlackReplyScan{False{}, True{}, 0}))

def black_terminal(+kind: U32, +wk: U32, +bk: U32,
  +pc: U32, +squares: List<&2, U32>) -> Bool:
  Bool.not(Retro.black_has_move(kind,
    Rules.State{wk, bk, pc, 1}, squares)) &&
  Rules.attacks(kind, pc, bk, wk)

def value.valid(+kind: U32, +clock: Nat,
  +state: Rules.State, +squares: List<&2, U32>,
  +next: ProofTree.Tree, +reset: ProofTree.Tree,
  +queen: ProofTree.Tree, +rook: ProofTree.Tree) -> Bool:
  match state:
    case Rules.State{wk, bk, pc, 0}:
      Nat.is_lt(clock, 100n) &&
      white_value(kind, wk, bk, pc, squares,
        next, reset, queen, rook)
    case Rules.State{wk, bk, pc, 1}:
      black_terminal(kind, wk, bk, pc, squares) ||
      (Nat.is_lt(clock, 100n) &&
        black_value(kind, wk, bk, pc, squares,
          next))
    case _:
      False{}

def value(+kind: U32, +clock: Nat,
  +state: Rules.State, +squares: List<&2, U32>,
  +next: ProofTree.Tree, +reset: ProofTree.Tree,
  +queen: ProofTree.Tree, +rook: ProofTree.Tree) -> Bool:
  Rules.valid(kind, state) &&
  Bool.not(U32.is_eq(kind, 2)) &&
  Bool.not(U32.is_eq(kind, 3)) &&
  value.valid(kind, clock, state, squares,
    next, reset, queen, rook)
