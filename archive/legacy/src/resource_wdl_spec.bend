import Base
import ./rules.bend as Rules
import ./wdl_spec.bend as WDL
import ./finite_wdl_spec.bend as Finite

# A strategy is a choice at White nodes and a response to every legal move at
# Black nodes. This is a Type-valued game semantics, independent of the table
# generator and of the Boolean minimax implementations. `remaining` counts
# plies before the next 100-halfmove claim. A legal pawn push resets it to 100
# while decreasing the strictly bounded number of pawn pushes.

def Nonpawn(remaining: Nat, +clock: Nat,
  +squares: List<&2, U32>,
  +kind: U32, state: Rules.State) -> Type:
  match remaining state:
    case 0n Rules.State{wk, bk, pc, 1}:
      WDL.BlackMate(kind, wk, bk, pc)
    case 0n _:
      Empty
    case 1n+rest Rules.State{wk, bk, pc, 0}:
      WDL.Truth(Rules.valid(kind,
        Rules.State{wk, bk, pc, 0})) &
      WDL.Truth(Nat.is_lt(clock, 100n)) &
      (Finite.SomeSquare(dest =>
         WDL.Truth(Rules.move_to(kind,
           Rules.State{wk, bk, pc, 0},
           Rules.State{dest, bk, pc, 1})) &
         Nonpawn(rest, 1n+clock,
           squares, kind,
           Rules.State{dest, bk, pc,
             1}), squares) |
       Finite.SomeSquare(dest =>
         WDL.Truth(Rules.move_to(kind,
           Rules.State{wk, bk, pc, 0},
           Rules.State{wk, bk, dest, 1})) &
         Nonpawn(rest, Bool.pick(Nat,
           U32.is_eq(kind, 4) &&
             U32.is_ne(pc, dest),
           0n, 1n+clock),
           squares, kind,
           Rules.State{wk, bk, dest,
             1}), squares))
    case 1n+rest Rules.State{wk, bk, pc, 1}:
      WDL.Truth(Rules.valid(kind,
        Rules.State{wk, bk, pc, 1})) &
      (WDL.BlackMate(kind, wk, bk, pc) |
       (WDL.Truth(Nat.is_lt(clock, 100n)) &
        Finite.SomeSquare(dest =>
          WDL.Truth(Rules.black_move(kind,
            wk, bk, pc, dest)),
          squares) &
        Finite.EverySquare(dest =>
          WDL.Truth(Rules.black_move(kind,
            wk, bk, pc, dest)) ->
          WDL.Truth(U32.is_ne(dest, pc)) &
          Nonpawn(rest, 1n+clock,
            squares, kind,
            Rules.State{wk, dest,
              pc, 0}), squares)))
    case 1n+rest _:
      Empty

# A scanner view of the same strategy type. It makes the proof of the
# executable move scan a structural induction over the candidate list.
type NonpawnTask is Data:
  WhiteValue{wk: U32, bk: U32,
    pc: U32, clock: Nat}
  BlackValue{wk: U32, bk: U32,
    pc: U32, clock: Nat}
  King{wk: U32, bk: U32, pc: U32,
    clock: Nat}
  Piece{wk: U32, bk: U32, pc: U32,
    clock: Nat}
  BlackAll{wk: U32, bk: U32,
    pc: U32, clock: Nat,
    all_so_far: Bool}

def NonpawnEvidence.phase(phase: Nat,
  task: NonpawnTask, n: Nat,
  +candidates: List<&2, U32>,
  +squares: List<&2, U32>,
  +kind: U32) -> Type:
  match phase task n:
    case 1n WhiteValue{wk, bk, pc,
           clock} _:
      Nonpawn(n, clock, squares,
        kind, Rules.State{wk,
          bk, pc, 0})
    case 1n BlackValue{wk, bk, pc,
           clock} _:
      Nonpawn(n, clock, squares,
        kind, Rules.State{wk,
          bk, pc, 1})
    case 0n King{wk, bk, pc, clock}
         1n+rest:
      Finite.SomeSquare(dest =>
        WDL.Truth(Rules.move_to(kind,
          Rules.State{wk, bk, pc, 0},
          Rules.State{dest, bk, pc,
            1})) &
        Nonpawn(rest, 1n+clock,
          squares, kind,
          Rules.State{dest, bk,
            pc, 1}), candidates)
    case 0n Piece{wk, bk, pc, clock}
         1n+rest:
      Finite.SomeSquare(dest =>
        WDL.Truth(Rules.move_to(kind,
          Rules.State{wk, bk, pc, 0},
          Rules.State{wk, bk, dest,
            1})) &
        Nonpawn(rest, Bool.pick(Nat,
          U32.is_eq(kind, 4) &&
            U32.is_ne(pc, dest),
          0n, 1n+clock),
          squares, kind,
          Rules.State{wk, bk,
            dest, 1}), candidates)
    case 0n BlackAll{wk, bk, pc,
           clock, all_so_far}
         1n+rest:
      WDL.Truth(all_so_far) &
      Finite.EverySquare(dest =>
        WDL.Truth(Rules.black_move(kind,
          wk, bk, pc, dest)) ->
        WDL.Truth(U32.is_ne(dest,
          pc)) &
        Nonpawn(rest, 1n+clock,
          squares, kind,
          Rules.State{wk, dest,
            pc, 0}), candidates)
    case _ _ _:
      Empty

def NonpawnEvidence(n: Nat, phase: Nat,
  +candidates: List<&2, U32>,
  +squares: List<&2, U32>,
  +kind: U32,
  task: NonpawnTask) -> Type:
  NonpawnEvidence.phase(phase, task,
    n, candidates, squares, kind)

# Keep the fixed post-promotion horizon behind a symbolic binder. Expanding
# Nonpawn(100n, ...) directly in a type makes the checker normalize the entire
# horizon even though the strategy theorem is uniform in fuel.
def Promoted(+squares: List<&2, U32>,
  +kind: U32, +wk: U32,
  +bk: U32, +pc: U32) -> Type:
  @fuel: Nat ->
    {fuel == 100n : Nat} ->
    Nonpawn(fuel, 0n, squares,
      kind,
      Rules.State{wk, bk, pc,
        1})

def Pawn(pushes: Nat, remaining: Nat,
  +squares: List<&2, U32>,
  state: Rules.State) -> Type:
  match pushes remaining state:
    case 0n _ _:
      Empty
    case 1n+push_rest 0n
         Rules.State{wk, bk, pc, 1}:
      WDL.BlackMate(4, wk, bk, pc)
    case 1n+push_rest 0n _:
      Empty
    case 1n++push_rest 1n++clock_rest
         Rules.State{wk, bk, pc, 0}:
      WDL.Truth(Rules.valid(4,
        Rules.State{wk, bk, pc, 0})) &
      ((Finite.SomeSquare(dest =>
          WDL.Truth(Rules.move_to(4,
            Rules.State{wk, bk, pc, 0},
            Rules.State{dest, bk,
              pc, 1})) &
          Pawn(1n+push_rest,
            clock_rest, squares,
            Rules.State{dest, bk,
              pc, 1}), squares) |
        Finite.SomeSquare(dest =>
          WDL.Truth(Rules.move_to(4,
            Rules.State{wk, bk, pc, 0},
            Rules.State{wk, bk,
              dest, 1})) &
          Pawn(push_rest, 100n,
            squares,
            Rules.State{wk, bk,
              dest, 1}), squares)) |
       ((WDL.Truth(WDL.promotion(wk, bk,
           pc, 0, wk, bk,
           (pc + 8 : U32))) &
         Promoted(squares, 0,
           wk, bk,
           (pc + 8 : U32))) |
        (WDL.Truth(WDL.promotion(wk, bk,
           pc, 1, wk, bk,
           (pc + 8 : U32))) &
         Promoted(squares, 1,
           wk, bk,
           (pc + 8 : U32)))))
    case 1n++push_rest 1n++clock_rest
         Rules.State{wk, bk, pc, 1}:
      WDL.Truth(Rules.valid(4,
        Rules.State{wk, bk, pc, 1})) &
      (WDL.BlackMate(4, wk, bk, pc) |
       (Finite.SomeSquare(dest =>
          WDL.Truth(Rules.black_move(4,
            wk, bk, pc, dest)),
          squares) &
        Finite.EverySquare(dest =>
          WDL.Truth(Rules.black_move(4,
            wk, bk, pc, dest)) ->
          WDL.Truth(U32.is_ne(dest,
            pc)) &
          Pawn(1n+push_rest,
            clock_rest, squares,
            Rules.State{wk, dest,
              pc, 0}), squares)))
    case 1n+push_rest 1n+clock_rest _:
      Empty

type PawnTask is Data:
  PawnWhiteValue{wk: U32, bk: U32,
    pc: U32}
  PawnBlackValue{wk: U32, bk: U32,
    pc: U32}
  PawnKing{wk: U32, bk: U32,
    pc: U32}
  PawnPiece{wk: U32, bk: U32,
    pc: U32}
  PawnBlackAll{wk: U32, bk: U32,
    pc: U32, all_so_far: Bool}

def PawnEvidence.phase(phase: Nat,
  task: PawnTask, pushes: Nat,
  remaining: Nat,
  +candidates: List<&2, U32>,
  +squares: List<&2, U32>) -> Type:
  match phase task pushes remaining:
    case 1n PawnWhiteValue{wk, bk, pc}
         _ _:
      Pawn(pushes, remaining,
        squares,
        Rules.State{wk, bk, pc,
          0})
    case 1n PawnBlackValue{wk, bk, pc}
         _ _:
      Pawn(pushes, remaining,
        squares,
        Rules.State{wk, bk, pc,
          1})
    case 0n PawnKing{wk, bk, pc}
         _ 1n+clock_rest:
      Finite.SomeSquare(dest =>
        WDL.Truth(Rules.move_to(4,
          Rules.State{wk, bk, pc,
            0},
          Rules.State{dest, bk,
            pc, 1})) &
        Pawn(pushes, clock_rest,
          squares,
          Rules.State{dest, bk,
            pc, 1}), candidates)
    case 0n PawnPiece{wk, bk, pc}
         0n 1n+clock_rest:
      Finite.SomeSquare(dest =>
        WDL.Truth(Rules.move_to(4,
          Rules.State{wk, bk, pc,
            0},
          Rules.State{wk, bk,
            dest, 1})) &
        Pawn(0n, clock_rest,
          squares,
          Rules.State{wk, bk,
            dest, 1}), candidates)
    case 0n PawnPiece{wk, bk, pc}
         1n+push_rest
         1n+clock_rest:
      Finite.SomeSquare(dest =>
        WDL.Truth(Rules.move_to(4,
          Rules.State{wk, bk, pc,
            0},
          Rules.State{wk, bk,
            dest, 1})) &
        Pawn(push_rest, 100n,
          squares,
          Rules.State{wk, bk,
            dest, 1}), candidates)
    case 0n PawnBlackAll{wk, bk, pc,
           all_so_far}
         _ 1n+clock_rest:
      WDL.Truth(all_so_far) &
      Finite.EverySquare(dest =>
        WDL.Truth(Rules.black_move(4,
          wk, bk, pc, dest)) ->
        WDL.Truth(U32.is_ne(dest,
          pc)) &
        Pawn(pushes, clock_rest,
          squares,
          Rules.State{wk, dest,
            pc, 0}), candidates)
    case _ _ _ _:
      Empty

def PawnEvidence(pushes: Nat,
  remaining: Nat, phase: Nat,
  +candidates: List<&2, U32>,
  +squares: List<&2, U32>,
  task: PawnTask) -> Type:
  PawnEvidence.phase(phase, task,
    pushes, remaining,
    candidates, squares)
