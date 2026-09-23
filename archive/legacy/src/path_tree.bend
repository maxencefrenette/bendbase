import Base

type Tree<-A: Data> is Data:
  Leaf{value: A}
  Node{left: Tree<A>, right: Tree<A>}

def Full(n: Nat, -A: Data,
  tree: Tree<A>) -> Type:
  match n tree:
    case 0n Leaf{value}:
      Unit
    case 0n Node{left, right}:
      Empty
    case 1n+rest Leaf{value}:
      Empty
    case 1n+rest Node{left, right}:
      Full(rest, A, left) &
      Full(rest, A, right)

def get(n: Nat, -A: Data, tree: Tree<A>,
  bits: Word(n)) -> A:
  match n tree bits:
    case 0n Leaf{value} WNil{}:
      value
    case 1n+rest Leaf{value} WCon{bit, tail}:
      value
    case 0n Node{left, right} WNil{}:
      get(0n, A, left, WNil{})
    case 1n+rest Node{left, right}
         WCon{False{}, tail}:
      get(rest, A, left, tail)
    case 1n+rest Node{left, right}
         WCon{True{}, tail}:
      get(rest, A, right, tail)

def prepend(+n: Nat, +bit: Bool,
  tree: Tree<Word(n)>) ->
  Tree<Word(1n+n)>:
  match tree:
    case Leaf{word}:
      Leaf{WCon{bit, word}}
    case Node{left, right}:
      Node{prepend(n, bit, left),
        prepend(n, bit, right)}

def drop_head(+n: Nat,
  tree: Tree<Word(1n+n)>) ->
  Tree<Word(n)>:
  match tree:
    case Leaf{WCon{bit, tail}}:
      Leaf{tail}
    case Node{left, right}:
      Node{drop_head(n, left),
        drop_head(n, right)}

# Each leaf of this full binary tree stores the path leading to it.
def paths(n: Nat) -> Tree<Word(n)>:
  match n:
    case 0n:
      Leaf{WNil{}}
    case 1n++rest:
      +children = paths(rest)
      Node{prepend(rest, False{}, children),
        prepend(rest, True{}, children)}
