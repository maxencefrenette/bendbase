import Base
import ./rules.bend as Rules
import ./wdl_spec.bend as WDL
import ./minimax_spec.bend as Minimax

# Direct perfect-play recursion with two explicit resources. `remaining` is
# 100 minus the halfmove clock; a pawn push or promotion restores it to 100
# while consuming one `pushes` token. A nonzeroing ply consumes one unit of
# `remaining`. For a three-man pawn, seven tokens exceed the number of legal
# pawn moves before promotion. The zero-token pawn case is deliberately a
# cutoff; the bound proof must show it is unreachable from a valid start.
type Task is Data:
  Value{kind: U32, state: Rules.State}
  King{kind: U32, wk: U32, bk: U32, pc: U32}
  Piece{kind: U32, wk: U32, bk: U32, pc: U32}
  BlackAll{kind: U32, wk: U32, bk: U32,
    pc: U32, all_so_far: Bool}

def win(+pushes: Nat, remaining: Nat,
  phase: Nat, +candidates: List<&2, U32>,
  +all_squares: List<&2, U32>,
  task: Task) -> Bool:
  match pushes remaining phase candidates task:
    case 0n 0n 1n _
         Value{+kind, state}:
      match state:
        case Rules.State{+wk, +bk, +pc, 1}:
          Bool.not(U32.is_eq(kind, 4)) &&
          Rules.valid(kind,
            Rules.State{wk, bk, pc, 1}) &&
          Bool.not(U32.is_eq(kind, 2)) &&
          Bool.not(U32.is_eq(kind, 3)) &&
          Bool.not(Minimax.has_move(all_squares,
            kind, wk, bk, pc, False{})) &&
          Rules.attacks(kind, pc, bk, wk)
        case _:
          False{}
    case 1n+push_rest 0n 1n _
         Value{+kind, state}:
      match state:
        case Rules.State{+wk, +bk, +pc, 1}:
          Rules.valid(kind,
            Rules.State{wk, bk, pc, 1}) &&
          Bool.not(U32.is_eq(kind, 2)) &&
          Bool.not(U32.is_eq(kind, 3)) &&
          Bool.not(Minimax.has_move(all_squares,
            kind, wk, bk, pc, False{})) &&
          Rules.attacks(kind, pc, bk, wk)
        case _:
          False{}
    case 0n 1n++clock_rest 1n _
         Value{+kind, state}:
      match state:
        case Rules.State{+wk, +bk, +pc, 0}:
          Bool.not(U32.is_eq(kind, 4)) &&
          Rules.valid(kind,
            Rules.State{wk, bk, pc, 0}) &&
          Bool.not(U32.is_eq(kind, 2)) &&
          Bool.not(U32.is_eq(kind, 3)) &&
          (win(0n, 1n+clock_rest,
              0n, all_squares,
              all_squares,
              King{kind, wk, bk, pc}) ||
           win(0n, 1n+clock_rest,
              0n, all_squares,
              all_squares,
              Piece{kind, wk, bk, pc}))
        case Rules.State{+wk, +bk, +pc, 1}:
          Bool.not(U32.is_eq(kind, 4)) &&
          Rules.valid(kind,
            Rules.State{wk, bk, pc, 1}) &&
          Bool.not(U32.is_eq(kind, 2)) &&
          Bool.not(U32.is_eq(kind, 3)) &&
          ((Bool.not(Minimax.has_move(
              all_squares, kind, wk, bk,
              pc, False{})) &&
            Rules.attacks(kind, pc, bk, wk)) ||
           (Minimax.has_move(all_squares,
              kind, wk, bk, pc, False{}) &&
            win(0n, 1n+clock_rest,
              0n, all_squares,
              all_squares,
              BlackAll{kind, wk, bk, pc,
                True{}})))
        case _:
          False{}
    case 1n++push_rest 1n++clock_rest
         1n _
         Value{+kind, state}:
      match state:
        case Rules.State{+wk, +bk, +pc, 0}:
          Rules.valid(kind,
            Rules.State{wk, bk, pc, 0}) &&
          Bool.not(U32.is_eq(kind, 2)) &&
          Bool.not(U32.is_eq(kind, 3)) &&
          (win(1n+push_rest,
              1n+clock_rest, 0n,
              all_squares, all_squares,
              King{kind, wk, bk, pc}) ||
           win(1n+push_rest,
              1n+clock_rest, 0n,
              all_squares, all_squares,
              Piece{kind, wk, bk, pc}) ||
           (U32.is_eq(kind, 4) &&
             ((WDL.promotion(wk, bk, pc,
                 0, wk, bk,
                 (pc + 8 : U32)) &&
               Minimax.value(100n, 0n,
                 all_squares, 0,
                 Rules.State{wk, bk,
                   (pc + 8 : U32), 1})) ||
              (WDL.promotion(wk, bk, pc,
                 1, wk, bk,
                 (pc + 8 : U32)) &&
               Minimax.value(100n, 0n,
                 all_squares, 1,
                 Rules.State{wk, bk,
                   (pc + 8 : U32), 1})))))
        case Rules.State{+wk, +bk, +pc, 1}:
          Rules.valid(kind,
            Rules.State{wk, bk, pc, 1}) &&
          Bool.not(U32.is_eq(kind, 2)) &&
          Bool.not(U32.is_eq(kind, 3)) &&
          ((Bool.not(Minimax.has_move(
              all_squares, kind, wk, bk,
              pc, False{})) &&
            Rules.attacks(kind, pc, bk, wk)) ||
           (Minimax.has_move(all_squares,
              kind, wk, bk, pc, False{}) &&
            win(1n+push_rest,
              1n+clock_rest, 0n,
              all_squares, all_squares,
              BlackAll{kind, wk, bk, pc,
                True{}})))
        case _:
          False{}
    case _ 1n+clock_rest 0n Nil{}
         King{kind, wk, bk, pc}:
      False{}
    case _ 1n++clock_rest 0n +dest <> tail
         King{+kind, +wk, +bk, +pc}:
      (Rules.move_to(kind,
          Rules.State{wk, bk, pc, 0},
          Rules.State{dest, bk, pc, 1}) &&
        win(pushes, clock_rest, 1n,
          all_squares, all_squares,
          Value{kind,
            Rules.State{dest, bk, pc,
              1}})) ||
      win(pushes, 1n+clock_rest, 0n,
        tail, all_squares,
        King{kind, wk, bk, pc})
    case 0n 1n+clock_rest 0n Nil{}
         Piece{kind, wk, bk, pc}:
      False{}
    case 0n 1n++clock_rest 0n +dest <> tail
         Piece{+kind, +wk, +bk, +pc}:
      (Rules.move_to(kind,
          Rules.State{wk, bk, pc, 0},
          Rules.State{wk, bk, dest, 1}) &&
        win(0n, clock_rest, 1n,
          all_squares, all_squares,
          Value{kind,
            Rules.State{wk, bk, dest,
              1}})) ||
      win(0n, 1n+clock_rest, 0n,
        tail, all_squares,
        Piece{kind, wk, bk, pc})
    case 1n+push_rest 1n+clock_rest 0n Nil{}
         Piece{kind, wk, bk, pc}:
      False{}
    case 1n++push_rest 1n++clock_rest
         0n +dest <> tail
         Piece{+kind, +wk, +bk, +pc}:
      +reset = U32.is_eq(kind, 4) &&
        U32.is_ne(pc, dest)
      (Rules.move_to(kind,
          Rules.State{wk, bk, pc, 0},
          Rules.State{wk, bk, dest, 1}) &&
        Bool.pick(Bool, reset,
          win(push_rest, 100n, 1n,
            all_squares, all_squares,
            Value{kind,
              Rules.State{wk, bk, dest,
                1}}),
          win(1n+push_rest, clock_rest,
            1n, all_squares, all_squares,
            Value{kind,
              Rules.State{wk, bk, dest,
                1}}))) ||
      win(1n+push_rest,
        1n+clock_rest, 0n, tail,
        all_squares,
        Piece{kind, wk, bk, pc})
    case _ 1n+clock_rest 0n Nil{}
         BlackAll{kind, wk, bk, pc,
           all_so_far}:
      all_so_far
    case _ 1n++clock_rest 0n +dest <> tail
         BlackAll{+kind, +wk, +bk, +pc,
           all_so_far}:
      win(pushes, 1n+clock_rest,
        0n, tail, all_squares,
        BlackAll{kind, wk, bk, pc,
          all_so_far &&
          (Bool.not(Rules.black_move(kind,
             wk, bk, pc, dest)) ||
           (U32.is_ne(dest, pc) &&
             win(pushes, clock_rest,
               1n, all_squares,
               all_squares, Value{kind,
                 Rules.State{wk, dest,
                   pc, 0}})))})
    case _ _ _ _ _:
      False{}

def value(pushes: Nat, remaining: Nat,
  +squares: List<&2, U32>, +kind: U32,
  +state: Rules.State) -> Bool:
  win(pushes, remaining, 1n,
    squares, squares,
    Value{kind, state})

def pawn_value_at_path(pushes: Nat,
  remaining: Nat,
  +squares: List<&2, U32>,
  path: Word(19n)) -> U32:
  Bool.pick(U32,
    value(pushes, remaining, squares,
      4, Rules.decode(
        Minimax.index_of_path(path))),
    1, 0)
