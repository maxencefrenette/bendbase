import Base

def flip_cmp(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

# Squares are six low bits. This is a structural, mixed-radix layout:
# WK[0..5], BK[6..11], piece[12..17], turn[18], then thirteen zero bits.

def ones(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{True{}, ones(p)}

def one(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{True{}, Word.zero(p)}

def cmp_low_zero(n: Nat, low: Word(n), high_cmp: Cmp) -> Cmp:
  match n:
    case 0n:
      high_cmp
    case 1n+p:
      match low:
        case WCon{bit, rest}:
          Word.cmp.fin(bit, False{},
            cmp_low_zero(p, rest, high_cmp))

def append(-m: Nat, n: Nat, w: Word(n), tail: Word(m)) ->
  Word(Nat.add(n, m)):
  match n:
    case 0n:
      tail
    case 1n+p:
      match w:
        case WCon{bit, rest}:
          WCon{bit, append(m, p, rest, tail)}

def mask6() -> U32:
  U32{append(26n, 6n, ones(6n), Word.zero(26n))}

def split.prepend(-n: Nat, -m: Nat, bit: Bool,
  pair: Word(n) & Word(m)) -> Word(1n+n) & Word(m):
  match pair:
    case (low, high):
      (WCon{bit, low}, high)

def split(-m: Nat, n: Nat, w: Word(Nat.add(n, m))) ->
  Word(n) & Word(m):
  match n:
    case 0n:
      (WNil{}, w)
    case 1n+p:
      match w:
        case WCon{bit, rest}:
          split.prepend(p, m, bit, split(m, p, rest))

def join(n: Nat, -m: Nat,
  pair: Word(n) & Word(m)) -> Word(Nat.add(n, m)):
  match pair:
    case (low, high):
      append(m, n, low, high)

def low6.fin(pair: Word(6n) & Word(26n)) -> Word(6n):
  match pair:
    case (low, high):
      low

def low6.of26(pair: Word(6n) & Word(20n)) -> Word(6n):
  match pair:
    case (low, high):
      low

def low6.of20(pair: Word(6n) & Word(14n)) -> Word(6n):
  match pair:
    case (low, high):
      low

def low6(x: U32) -> Word(6n):
  match x:
    case U32{w}:
      low6.fin(split(26n, 6n, w))

def low1(x: U32) -> Bool:
  match x:
    case U32{w}:
      match w:
        case WCon{bit, rest}:
          bit

def low1.fin(pair: Word(1n) & Word(31n)) -> Bool:
  match pair:
    case (WCon{bit, WNil{}}, high):
      bit

def square(bits: Word(6n)) -> U32:
  U32{append(26n, 6n, bits, Word.zero(26n))}

def field1(bits: Word(6n)) -> U32:
  U32{append(26n, 6n, Word.zero(6n),
    append(20n, 6n, bits, Word.zero(20n)))}

def field2(bits: Word(6n)) -> U32:
  U32{append(20n, 12n, Word.zero(12n),
    append(14n, 6n, bits, Word.zero(14n)))}

def field3(bit: Bool) -> U32:
  U32{append(14n, 18n, Word.zero(18n),
    WCon{bit, Word.zero(13n)})}

# Shift a fixed-width word by repeatedly discarding its low bit. The outer
# form exposes one discarded source bit first; the inner form mirrors U32.shrn.
def shrn.outer(+size: Nat, count: Nat, word: Word(size)) -> Word(size):
  match count:
    case 0n:
      word
    case 1n+rest:
      shrn.outer(size, rest, Word.shr(size, word))

def shrn.inner(+size: Nat, count: Nat, word: Word(size)) -> Word(size):
  match count:
    case 0n:
      word
    case 1n+rest:
      Word.shr(size, shrn.inner(size, rest, word))

def padn(+size: Nat, count: Nat, word: Word(size)) ->
  Word(Nat.add(count, size)):
  match count:
    case 0n:
      word
    case 1n++rest:
      Word.shr.pad(Nat.add(rest, size), padn(size, rest, word))

def turn(bits: Word(14n)) -> U32:
  U32{append(18n, 14n, bits, Word.zero(18n))}

def index(wk: U32, bk: U32, pc: U32, turn: U32) -> U32:
  U32{append(26n, 6n, low6(wk),
    append(20n, 6n, low6(bk),
      append(14n, 6n, low6(pc),
        WCon{low1(turn), Word.zero(13n)})))}

def decode.pc(wk: Word(6n), bk: Word(6n),
  pair: Word(6n) & Word(14n)) -> U32 & U32 & U32 & U32:
  match pair:
    case (pc, rest14):
      (square(wk), square(bk), square(pc), turn(rest14))

def decode.bk(wk: Word(6n),
  pair: Word(6n) & Word(20n)) -> U32 & U32 & U32 & U32:
  match pair:
    case (bk, rest20):
      decode.pc(wk, bk, split(14n, 6n, rest20))

def decode.wk(pair: Word(6n) & Word(26n)) ->
  U32 & U32 & U32 & U32:
  match pair:
    case (wk, rest26):
      decode.bk(wk, split(20n, 6n, rest26))

def decode(+i: U32) -> U32 & U32 & U32 & U32:
  match i:
    case U32{w}:
      decode.wk(split(26n, 6n, w))

def chunks.pc(wk: Word(6n), bk: Word(6n),
  pair: Word(6n) & Word(14n)) ->
  Word(6n) & Word(6n) & Word(6n) & Word(14n):
  match pair:
    case (pc, high):
      (wk, bk, pc, high)

def chunks.bk(wk: Word(6n),
  pair: Word(6n) & Word(20n)) ->
  Word(6n) & Word(6n) & Word(6n) & Word(14n):
  match pair:
    case (bk, rest):
      chunks.pc(wk, bk, split(14n, 6n, rest))

def chunks.wk(pair: Word(6n) & Word(26n)) ->
  Word(6n) & Word(6n) & Word(6n) & Word(14n):
  match pair:
    case (wk, rest):
      chunks.bk(wk, split(20n, 6n, rest))

def chunks(word: Word(32n)) ->
  Word(6n) & Word(6n) & Word(6n) & Word(14n):
  chunks.wk(split(26n, 6n, word))

def pack(wk: Word(6n), bk: Word(6n), pc: Word(6n),
  high: Word(14n)) -> Word(32n):
  append(26n, 6n, wk,
    append(20n, 6n, bk,
      append(14n, 6n, pc, high)))

def pack.parts(parts: Word(6n) & Word(6n) & Word(6n) & Word(14n)) ->
  Word(32n):
  match parts:
    case (wk, bk, pc, high):
      pack(wk, bk, pc, high)

def truncate19.fin(pair: Word(19n) & Word(13n)) -> U32:
  match pair:
    case (low, high):
      U32{append(13n, 19n, low, Word.zero(13n))}

def low19.fin(pair: Word(19n) & Word(13n)) -> Word(19n):
  match pair:
    case (low, high):
      low

def truncate19(i: U32) -> U32:
  match i:
    case U32{word}:
      truncate19.fin(split(13n, 19n, word))

def mask19() -> U32:
  U32{append(13n, 19n, ones(19n), Word.zero(13n))}
