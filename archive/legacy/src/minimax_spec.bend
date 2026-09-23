import Base
import ./rules.bend as Rules
import ./wdl_spec.bend as WDL
import ./encoding.bend as Encoding
import ./clocked_index.bend as ClockedIndex

# A direct, scalar minimax specification. This code has no table reads or
# retrograde state. `fuel` counts remaining plies; `phase` is one for a game
# state and zero while scanning candidate moves. Every recursive call either
# decreases fuel, decreases phase, or shortens candidates. Thus no position
# enumeration occurs when the proof checker reasons about this definition.
type Task is Data:
  Value{kind: U32, state: Rules.State, clock: Nat}
  King{kind: U32, wk: U32, bk: U32, pc: U32, clock: Nat}
  Piece{kind: U32, wk: U32, bk: U32, pc: U32, clock: Nat}
  BlackAll{kind: U32, wk: U32, bk: U32, pc: U32,
    clock: Nat, all_so_far: Bool}

def has_move(candidates: List<&2, U32>,
  +kind: U32, +wk: U32, +bk: U32,
  +pc: U32, found: Bool) -> Bool:
  match candidates:
    case Nil{}:
      found
    case dest <> tail:
      has_move(tail, kind, wk, bk, pc,
        found || Rules.black_move(kind,
          wk, bk, pc, dest))

def win(fuel: Nat, phase: Nat,
  +candidates: List<&2, U32>,
  +all_squares: List<&2, U32>,
  task: Task) -> Bool:
  match fuel phase candidates task:
    case 0n 1n _ Value{+kind, state, clock}:
      match state:
        case Rules.State{+wk, +bk, +pc, 1}:
          Rules.valid(kind,
            Rules.State{wk, bk, pc, 1}) &&
          Bool.not(U32.is_eq(kind, 2)) &&
          Bool.not(U32.is_eq(kind, 3)) &&
          Bool.not(has_move(all_squares, kind,
            wk, bk, pc, False{})) &&
          Rules.attacks(kind, pc, bk, wk)
        case _:
          False{}
    case 1n++rest 1n _ Value{+kind, state, +clock}:
      match state:
        case Rules.State{+wk, +bk, +pc, 0}:
          Rules.valid(kind,
            Rules.State{wk, bk, pc, 0}) &&
          Bool.not(U32.is_eq(kind, 2)) &&
          Bool.not(U32.is_eq(kind, 3)) &&
          Nat.is_lt(clock, 100n) &&
          (win(1n+rest, 0n,
              all_squares, all_squares,
              King{kind, wk, bk, pc, clock}) ||
           win(1n+rest, 0n,
              all_squares, all_squares,
              Piece{kind, wk, bk, pc, clock}) ||
           (U32.is_eq(kind, 4) &&
             (WDL.promotion(wk, bk, pc, 0,
                wk, bk, (pc + 8 : U32)) &&
               win(rest, 1n, all_squares,
                 all_squares, Value{0,
                   Rules.State{wk, bk,
                     (pc + 8 : U32), 1}, 0n}) ||
              WDL.promotion(wk, bk, pc, 1,
                wk, bk, (pc + 8 : U32)) &&
               win(rest, 1n, all_squares,
                 all_squares, Value{1,
                   Rules.State{wk, bk,
                     (pc + 8 : U32), 1}, 0n}))))
        case Rules.State{+wk, +bk, +pc, 1}:
          Rules.valid(kind,
            Rules.State{wk, bk, pc, 1}) &&
          Bool.not(U32.is_eq(kind, 2)) &&
          Bool.not(U32.is_eq(kind, 3)) &&
          ((Bool.not(has_move(all_squares,
              kind, wk, bk, pc, False{})) &&
            Rules.attacks(kind, pc, bk, wk)) ||
           (Nat.is_lt(clock, 100n) &&
            has_move(all_squares, kind, wk,
              bk, pc, False{}) &&
            win(1n+rest, 0n,
              all_squares, all_squares,
              BlackAll{kind, wk, bk, pc,
                clock, True{}})))
        case _:
          False{}
    case 1n+rest 0n Nil{} King{kind, wk, bk,
         pc, clock}:
      False{}
    case 1n++rest 0n +dest <> tail King{+kind,
         +wk, +bk, +pc, +clock}:
      (Rules.move_to(kind,
          Rules.State{wk, bk, pc, 0},
          Rules.State{dest, bk, pc, 1}) &&
        win(rest, 1n, all_squares,
          all_squares, Value{kind,
            Rules.State{dest, bk, pc, 1},
            1n+clock})) ||
      win(1n+rest, 0n, tail,
        all_squares,
        King{kind, wk, bk, pc, clock})
    case 1n+rest 0n Nil{} Piece{kind, wk,
         bk, pc, clock}:
      False{}
    case 1n++rest 0n +dest <> tail Piece{+kind,
         +wk, +bk, +pc, +clock}:
      +reset = U32.is_eq(kind, 4) &&
        U32.is_ne(pc, dest)
      (Rules.move_to(kind,
          Rules.State{wk, bk, pc, 0},
          Rules.State{wk, bk, dest, 1}) &&
        win(rest, 1n, all_squares,
          all_squares, Value{kind,
            Rules.State{wk, bk, dest, 1},
            Bool.pick(Nat, reset, 0n,
              1n+clock)})) ||
      win(1n+rest, 0n, tail,
        all_squares,
        Piece{kind, wk, bk, pc, clock})
    case 1n+rest 0n Nil{} BlackAll{kind, wk,
         bk, pc, clock, all_so_far}:
      all_so_far
    case 1n++rest 0n +dest <> tail BlackAll{+kind,
         +wk, +bk, +pc, +clock, all_so_far}:
      win(1n+rest, 0n, tail,
        all_squares,
        BlackAll{kind, wk, bk, pc, clock,
          all_so_far &&
          (Bool.not(Rules.black_move(kind,
             wk, bk, pc, dest)) ||
           (U32.is_ne(dest, pc) &&
             win(rest, 1n, all_squares,
               all_squares, Value{kind,
                 Rules.State{wk, dest, pc, 0},
                 1n+clock})))})
    case _ _ _ _:
      False{}

def value(fuel: Nat, +clock: Nat,
  +squares: List<&2, U32>, +kind: U32,
  +state: Rules.State) -> Bool:
  win(fuel, 1n, squares, squares,
    Value{kind, state, clock})

def index_of_path(path: Word(19n)) -> U32:
  U32{Encoding.append(13n, 19n,
    ClockedIndex.reverse(19n, path),
    Word.zero(13n))}

def value_at_path(fuel: Nat, +clock: Nat,
  +squares: List<&2, U32>, +kind: U32,
  path: Word(19n)) -> U32:
  Bool.pick(U32, value(fuel, clock, squares,
    kind, Rules.decode(index_of_path(path))),
    1, 0)
