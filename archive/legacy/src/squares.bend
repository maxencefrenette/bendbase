import Base
import ./encoding.bend as Encoding

# Enumerate n-bit words by branching on the next bit. In particular, all6
# enumerates the 64 squares without spelling out any board position.
def prefix(n: Nat, +bit: Bool,
  xs: List<&2, Word(n)>) -> List<&2, Word(1n+n)>:
  match xs:
    case Nil{}:
      Nil{}
    case head <> tail:
      WCon{bit, head} <> prefix(n, bit, tail)

def words(n: Nat) -> List<&2, Word(n)>:
  match n:
    case 0n:
      WNil{} <> Nil{}
    case 1n++rest:
      List.append(&2, Word(1n+rest),
        prefix(rest, False{}, words(rest)),
        prefix(rest, True{}, words(rest)))

def encode(xs: List<&2, Word(6n)>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case head <> tail:
      Encoding.square(head) <> encode(tail)

def all6() -> List<&2, U32>:
  encode(words(6n))

def equals(xs: List<&2, U32>,
  ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case x <> rest y <> tail:
      U32.is_eq(x, y) &&
        equals(rest, tail)
    case _ _:
      False{}

def Member(-A: Data, x: A, xs: List<&2, A>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case head <> tail:
      {x == head : A} | Member(A, x, tail)
