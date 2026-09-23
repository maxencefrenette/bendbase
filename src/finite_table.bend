import Base

# A total table over n-bit keys. Its size is part of its type.
law Table:
  for n: Nat
  for A: Data
  Data

type Branch<-depth: Nat, -A: Data> is Data:
  Fork{left: Table(depth, A), right: Table(depth, A)}

def Table(n, A):
  match n:
    case 0n:
      A
    case 1n+rest:
      Branch<rest, A>

def get(n: Nat, -A: Data, key: Word(n), table: Table(n, A)) -> A:
  match n key table:
    case 0n WNil{} value:
      value
    case 1n+rest WCon{False{}, tail} Fork{left, right}:
      get(rest, A, tail, left)
    case 1n+rest WCon{True{}, tail} Fork{left, right}:
      get(rest, A, tail, right)

def prepend(depth: Nat, +width: Nat, +bit: Bool,
  table: Table(depth, Word(width))) -> Table(depth, Word(1n+width)):
  match depth table:
    case 0n word:
      WCon{bit, word}
    case 1n++rest Fork{left, right}:
      Fork{prepend(rest, width, bit, left),
       prepend(rest, width, bit, right)}

def keys(n: Nat) -> Table(n, Word(n)):
  match n:
    case 0n:
      WNil{}
    case 1n++rest:
      +tail = keys(rest)
      Fork{prepend(rest, rest, False{}, tail),
       prepend(rest, rest, True{}, tail)}

def size(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n++rest:
      Nat.add(size(rest), size(rest))

def offset(n: Nat, key: Word(n)) -> Nat:
  match n key:
    case 0n WNil{}:
      0n
    case 1n+rest WCon{False{}, tail}:
      offset(rest, tail)
    case 1n++rest WCon{True{}, tail}:
      Nat.add(size(rest), offset(rest, tail))

def flatten.go(n: Nat, table: Table(n, U32), acc: List<&2, U32>) -> List<&2, U32>:
  match n table:
    case 0n byte:
      byte <> acc
    case 1n++rest Fork{left, right}:
      flatten.go(rest, left, flatten.go(rest, right, acc))

def flatten(n: Nat, table: Table(n, U32)) -> List<&2, U32>:
  flatten.go(n, table, Nil{})

def read(bytes: List<&2, U32>, offset: Nat) -> Maybe<&2, U32>:
  match bytes offset:
    case Nil{} _:
      None{}
    case head <> tail 0n:
      Some{head}
    case head <> tail 1n+rest:
      read(tail, rest)
