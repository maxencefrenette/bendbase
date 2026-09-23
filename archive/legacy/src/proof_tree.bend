import Base
import ./encoding.bend as Encoding

# A persistent table for the proof-first solver. Unlike Base.Array, this tree
# is Data: a proof may refer to the same subtree in the read and write laws.
# The word is traversed most-significant-index-bit first, matching Base.Array's
# left/right layout when the finished tree is converted for serialization.
type Tree is Data:
  Leaf{value: U32}
  Node{left: Tree, right: Tree}

def Full(n: Nat, +tree: Tree) -> Type:
  match n tree:
    case 0n Leaf{value}:
      Unit
    case 0n Node{left, right}:
      Empty
    case 1n+rest Leaf{value}:
      Empty
    case 1n+rest Node{left, right}:
      Full(rest, left) & Full(rest, right)

def filled(depth: Nat, +value: U32) -> Tree:
  match depth:
    case 0n:
      Leaf{value}
    case 1n++rest:
      Node{filled(rest, value), filled(rest, value)}

def get(n: Nat, +tree: Tree, bits: Word(n)) -> U32:
  match n tree bits:
    case 0n Leaf{value} WNil{}:
      value
    case 1n+rest Leaf{value} WCon{bit, tail}:
      value
    case 0n Node{left, right} WNil{}:
      get(0n, left, WNil{})
    case 1n+rest Node{left, right} WCon{False{}, tail}:
      get(rest, left, tail)
    case 1n+rest Node{left, right} WCon{True{}, tail}:
      get(rest, right, tail)

def set(n: Nat, +tree: Tree, bits: Word(n), +value: U32) -> Tree:
  match n tree bits:
    case 0n Leaf{old} WNil{}:
      Leaf{value}
    case 1n+rest Leaf{old} WCon{bit, tail}:
      Leaf{value}
    case 0n Node{left, right} WNil{}:
      Node{set(0n, left, WNil{}, value), right}
    case 1n+rest Node{left, right} WCon{False{}, tail}:
      Node{set(rest, left, tail, value), right}
    case 1n+rest Node{left, right} WCon{True{}, tail}:
      Node{left, set(rest, right, tail, value)}

def bits_desc(count: Nat, +index: U32) -> Word(count):
  match count:
    case 0n:
      WNil{}
    case 1n++rest:
      WCon{Encoding.low1(U32.shrn(index, rest)),
        bits_desc(rest, index)}

def bits19(index: U32) -> Word(19n):
  bits_desc(19n, index)

def get_index(+tree: Tree, index: U32) -> U32:
  get(19n, tree, bits19(index))

def set_index(+tree: Tree, index: U32, value: U32) -> Tree:
  set(19n, tree, bits19(index), value)

def to_array(tree: Tree) -> Array<U32>:
  match tree:
    case Leaf{value}:
      ALeaf{value}
    case Node{left, right}:
      ANode{to_array(left), to_array(right)}

# This is the logical byte order of a tree. The serializer's correspondence
# with this function is proved in PROOF.bend, without visiting a concrete file.
def bytes.go(tree: Tree, acc: List<&2, U32>) -> List<&2, U32>:
  match tree:
    case Leaf{value}:
      value <> acc
    case Node{left, right}:
      bytes.go(left, bytes.go(right, acc))

def bytes(tree: Tree) -> List<&2, U32>:
  bytes.go(tree, Nil{})

def slot_count(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n++rest:
      Nat.add(slot_count(rest),
        slot_count(rest))

# Natural-number offset into the left-to-right byte sequence for an
# MSB-first tree path. This is a format specification, not an index scan.
def byte_offset(n: Nat,
  bits: Word(n)) -> Nat:
  match n bits:
    case 0n WNil{}:
      0n
    case 1n++rest WCon{False{}, tail}:
      byte_offset(rest, tail)
    case 1n++rest WCon{True{}, tail}:
      Nat.add(slot_count(rest),
        byte_offset(rest, tail))
