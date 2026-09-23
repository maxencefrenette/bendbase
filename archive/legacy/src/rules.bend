import Base
import ./position.bend as Position

# Classes: 0 queen, 1 rook, 2 bishop, 3 knight, 4 pawn.
# Turns: 0 white (the side with the extra piece), 1 black.
# The index has exactly 2^19 possible values.
type State is Data:
  State{wk: U32, bk: U32, pc: U32, turn: U32}

def index(s: State) -> U32:
  match s:
    case State{wk, bk, pc, turn}:
      U32.or(U32.or(U32.or(
        U32.and(wk, 63),
        U32.shln(U32.and(bk, 63), 6n)),
        U32.shln(U32.and(pc, 63), 12n)),
        U32.shln(U32.and(turn, 1), 18n))

def decode(+i: U32) -> State:
  State{U32.and(i, 63),
    U32.and(U32.shrn(i, 6n), 63),
    U32.and(U32.shrn(i, 12n), 63),
    U32.shrn(i, 18n)}

def file(s: U32) -> U32:
  U32.and(s, 7)

def rank(s: U32) -> U32:
  U32.shrn(s, 3n)

def between(+x: U32, +a: U32, +b: U32) -> Bool:
  U32.is_lt(U32.min(a, b), x) && U32.is_lt(x, U32.max(a, b))

def same_file(a: U32, b: U32) -> Bool:
  U32.is_eq(file(a), file(b))

def same_rank(a: U32, b: U32) -> Bool:
  U32.is_eq(rank(a), rank(b))

def bishop_line(+a: U32, +b: U32) -> Bool:
  U32.is_eq(Position.distance(file(a), file(b)),
    Position.distance(rank(a), rank(b)))

def rook_line(+a: U32, +b: U32) -> Bool:
  same_file(a, b) || same_rank(a, b)

# Only a king can block a ray in a three-man position.
def on_segment(+a: U32, +b: U32, +x: U32) -> Bool:
  (same_rank(a, b) && same_rank(a, x) &&
    between(file(x), file(a), file(b))) ||
  (same_file(a, b) && same_file(a, x) &&
    between(rank(x), rank(a), rank(b))) ||
  (bishop_line(a, b) && bishop_line(a, x) &&
    between(file(x), file(a), file(b)) &&
    between(rank(x), rank(a), rank(b)))

def knight_jump(+a: U32, +b: U32) -> Bool:
  +dx = Position.distance(file(a), file(b))
  +dy = Position.distance(rank(a), rank(b))
  (U32.is_eq(dx, 1) && U32.is_eq(dy, 2)) ||
  (U32.is_eq(dx, 2) && U32.is_eq(dy, 1))

def pawn_attacks(+a: U32, +b: U32) -> Bool:
  U32.is_eq(rank(b), (rank(a) + 1 : U32)) &&
  U32.is_eq(Position.distance(file(a), file(b)), 1)

def line_attack(+kind: U32, +a: U32, +b: U32) -> Bool:
  (U32.is_eq(kind, 0) && (rook_line(a, b) || bishop_line(a, b))) ||
  (U32.is_eq(kind, 1) && rook_line(a, b)) ||
  (U32.is_eq(kind, 2) && bishop_line(a, b))

def attacks(+kind: U32, +pc: U32, +target: U32, +wk: U32) -> Bool:
  U32.is_ne(pc, target) &&
  ((line_attack(kind, pc, target) && Bool.not(on_segment(pc, target, wk))) ||
   (U32.is_eq(kind, 3) && knight_jump(pc, target)) ||
   (U32.is_eq(kind, 4) && pawn_attacks(pc, target)))

def placement_valid(+kind: U32, +wk: U32, +bk: U32,
  +pc: U32, +turn: U32) -> Bool:
  U32.is_lt(kind, 5) && U32.is_lt(turn, 2) &&
  U32.is_lt(wk, 64) && U32.is_lt(bk, 64) && U32.is_lt(pc, 64) &&
  U32.is_ne(wk, bk) && U32.is_ne(wk, pc) && U32.is_ne(bk, pc)

def valid(+kind: U32, s: State) -> Bool:
  match s:
    case State{+wk, +bk, +pc, +turn}:
      placement_valid(kind, wk, bk, pc, turn) &&
      Bool.not(Position.kings_touch(wk, bk)) &&
      (Bool.not(U32.is_eq(kind, 4)) ||
        (U32.is_gt(rank(pc), 0) && U32.is_lt(rank(pc), 7))) &&
      (U32.is_eq(turn, 1) || Bool.not(attacks(kind, pc, bk, wk)))

def king_step(+a: U32, +b: U32) -> Bool:
  U32.is_ne(a, b) && Position.kings_touch(a, b)

def pawn_step(+from: U32, +to: U32, +wk: U32, +bk: U32) -> Bool:
  (U32.is_eq(to, (from + 8 : U32)) && U32.is_ne(to, wk) &&
    U32.is_ne(to, bk) && U32.is_lt(rank(to), 7)) ||
  (U32.is_eq(rank(from), 1) && U32.is_eq(to, (from + 16 : U32)) &&
    U32.is_ne((from + 8 : U32), wk) &&
    U32.is_ne((from + 8 : U32), bk) &&
    U32.is_ne(to, wk) && U32.is_ne(to, bk))

def pawn_can_promote(+wk: U32, +bk: U32, +pc: U32) -> Bool:
  +target = (pc + 8 : U32)
  valid(4, State{wk, bk, pc, 0}) &&
  U32.is_eq(rank(pc), 6) &&
  U32.is_ne(target, wk) && U32.is_ne(target, bk)

def piece_step(+kind: U32, +from: U32, +to: U32, +wk: U32,
  +bk: U32) -> Bool:
  U32.is_ne(from, to) &&
  ((U32.is_eq(kind, 4) && pawn_step(from, to, wk, bk)) ||
   (U32.is_eq(kind, 3) && knight_jump(from, to)) ||
   (line_attack(kind, from, to) &&
     Bool.not(on_segment(from, to, wk)) &&
     Bool.not(on_segment(from, to, bk))))

# Same-class move; captures and promotions leave this state graph.
def move_to(+kind: U32, from: State, to: State) -> Bool:
  match from to:
    case State{+wk, +bk, +pc, 0} State{+wk2, +bk2, +pc2, 1}:
      valid(kind, State{wk, bk, pc, 0}) &&
      valid(kind, State{wk2, bk2, pc2, 1}) &&
      U32.is_eq(bk, bk2) &&
      ((U32.is_eq(pc, pc2) && king_step(wk, wk2)) ||
       (U32.is_eq(wk, wk2) && piece_step(kind, pc, pc2, wk, bk)))
    case State{+wk, +bk, +pc, 1} State{+wk2, +bk2, +pc2, 0}:
      valid(kind, State{wk, bk, pc, 1}) &&
      valid(kind, State{wk2, bk2, pc2, 0}) &&
      U32.is_eq(wk, wk2) && U32.is_eq(pc, pc2) &&
      king_step(bk, bk2)
    case _ _:
      False{}

# A king capture exits the three-man graph into the drawn K vs K ending.
def black_move(+kind: U32, +wk: U32, +bk: U32, +pc: U32,
  +dest: U32) -> Bool:
  king_step(bk, dest) &&
  Bool.not(Position.kings_touch(wk, dest)) &&
  (U32.is_eq(dest, pc) || valid(kind, State{wk, dest, pc, 0}))
