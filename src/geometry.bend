import Base

# The board geometry used by the pawnless chess rules. Squares are a1=0 to h8=63.
def file(square: U32) -> U32:
  U32.and(square, 7)

def rank(square: U32) -> U32:
  U32.shrn(square, 3n)

def distance(+a: U32, +b: U32) -> U32:
  (U32.max(a, b) - U32.min(a, b) : U32)

def kings_touch(+a: U32, +b: U32) -> Bool:
  U32.is_le(distance(file(a), file(b)), 1) && U32.is_le(distance(rank(a), rank(b)), 1)

def king_step(+a: U32, +b: U32) -> Bool:
  U32.is_ne(a, b) && kings_touch(a, b)

def between(+x: U32, +a: U32, +b: U32) -> Bool:
  U32.is_lt(U32.min(a, b), x) && U32.is_lt(x, U32.max(a, b))

def same_file(a: U32, b: U32) -> Bool:
  U32.is_eq(file(a), file(b))

def same_rank(a: U32, b: U32) -> Bool:
  U32.is_eq(rank(a), rank(b))

def bishop_line(+a: U32, +b: U32) -> Bool:
  U32.is_eq(distance(file(a), file(b)), distance(rank(a), rank(b)))

def rook_line(+a: U32, +b: U32) -> Bool:
  same_file(a, b) || same_rank(a, b)

def on_segment(+a: U32, +b: U32, +x: U32) -> Bool:
  (same_rank(a, b) && same_rank(a, x) && between(file(x), file(a), file(b))) ||
  (same_file(a, b) && same_file(a, x) && between(rank(x), rank(a), rank(b))) ||
  (bishop_line(a, b) && bishop_line(a, x) &&
    between(file(x), file(a), file(b)) && between(rank(x), rank(a), rank(b)))

def knight_jump(+a: U32, +b: U32) -> Bool:
  +dx = distance(file(a), file(b))
  +dy = distance(rank(a), rank(b))
  (U32.is_eq(dx, 1) && U32.is_eq(dy, 2)) || (U32.is_eq(dx, 2) && U32.is_eq(dy, 1))

# 0 queen, 1 rook, 2 bishop, 3 knight; Material supplies only these values.
def line_attack(+kind: U32, +a: U32, +b: U32) -> Bool:
  (U32.is_eq(kind, 0) && (rook_line(a, b) || bishop_line(a, b))) ||
  (U32.is_eq(kind, 1) && rook_line(a, b)) ||
  (U32.is_eq(kind, 2) && bishop_line(a, b))

def attacks(+kind: U32, +pc: U32, +target: U32, +own_king: U32) -> Bool:
  U32.is_ne(pc, target) &&
  ((line_attack(kind, pc, target) && Bool.not(on_segment(pc, target, own_king))) ||
   (U32.is_eq(kind, 3) && knight_jump(pc, target)))

def piece_step(+kind: U32, +from: U32, +to: U32, +wk: U32, +bk: U32) -> Bool:
  U32.is_ne(from, to) &&
  ((U32.is_eq(kind, 3) && knight_jump(from, to)) ||
   (line_attack(kind, from, to) && Bool.not(on_segment(from, to, wk)) && Bool.not(on_segment(from, to, bk))))
