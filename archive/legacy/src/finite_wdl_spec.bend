import Base
import ./rules.bend as Rules
import ./wdl_spec.bend as WDL
import ./clocked_wdl_spec.bend as Clocked

# Branching quantifiers over a structurally complete list of squares. These
# encode move choices, not a check of all table entries. In particular the
# Black branch is a product, so its evidence can be split by list induction.
def SomeSquare(-P: U32 -> Type,
  squares: List<&2, U32>) -> Type:
  match squares:
    case Nil{}:
      Empty
    case head <> rest:
      P(head) | SomeSquare(P, rest)

def EverySquare(-P: U32 -> Type,
  squares: List<&2, U32>) -> Type:
  match squares:
    case Nil{}:
      Unit
    case head <> rest:
      P(head) & EverySquare(P, rest)

# A finite-horizon White-win game, with the halfmove clock made explicit.
# A pawn push and every promotion reset the clock. Black's capture exits to a
# draw, so a winning Black-turn strategy must refute any legal capture.
# The current n counts plies; at n=0 only an already-present mate wins.
def WinWithin(n: Nat, clock: Nat,
  +squares: List<&2, U32>,
  +game: WDL.Game) -> Type:
  match n game:
    case 0n WDL.Black{kind, wk, bk, pc}:
      WDL.BlackMate(kind, wk, bk, pc)
    case 0n _:
      Empty
    case 1n+rest WDL.White{+kind, +wk, +bk, +pc}:
      WDL.Truth(Rules.valid(kind,
        Rules.State{wk, bk, pc, 0})) &
      WDL.Truth(Nat.is_lt(clock, 100n)) &
      (SomeSquare(dest =>
        WDL.Truth(Rules.move_to(kind,
          Rules.State{wk, bk, pc, 0},
          Rules.State{dest, bk, pc, 1})) &
        WinWithin(rest, 1n+clock, squares,
          WDL.Black{kind, dest, bk, pc}), squares) |
       SomeSquare(dest =>
        WDL.Truth(Rules.move_to(kind,
          Rules.State{wk, bk, pc, 0},
          Rules.State{wk, bk, dest, 1})) &
        WinWithin(rest,
          Clocked.next_clock(clock,
            WDL.White{kind, wk, bk, pc},
            WDL.Black{kind, wk, bk, dest}),
          squares, WDL.Black{kind, wk, bk, dest}),
          squares) |
       (WDL.Truth(U32.is_eq(kind, 4)) &
        WDL.Truth(WDL.promotion(wk, bk, pc,
          0, wk, bk, (pc + 8 : U32))) &
        WinWithin(rest, 0n, squares,
          WDL.Black{0, wk, bk, (pc + 8 : U32)})) |
       (WDL.Truth(U32.is_eq(kind, 4)) &
        WDL.Truth(WDL.promotion(wk, bk, pc,
          1, wk, bk, (pc + 8 : U32))) &
        WinWithin(rest, 0n, squares,
          WDL.Black{1, wk, bk, (pc + 8 : U32)})))
    case 1n+rest WDL.Black{+kind, +wk, +bk, +pc}:
      WDL.Truth(Rules.valid(kind,
        Rules.State{wk, bk, pc, 1})) &
      (WDL.BlackMate(kind, wk, bk, pc) |
      (WDL.Truth(Nat.is_lt(clock, 100n)) &
       SomeSquare(dest =>
         WDL.Truth(Rules.black_move(kind, wk,
           bk, pc, dest)), squares) &
       EverySquare(dest =>
         WDL.Truth(Rules.black_move(kind, wk,
           bk, pc, dest)) ->
         WDL.Truth(U32.is_ne(dest, pc)) &
         WinWithin(rest, 1n+clock, squares,
           WDL.White{kind, wk, dest, pc}),
         squares)))
    case 1n+rest _:
      Empty
