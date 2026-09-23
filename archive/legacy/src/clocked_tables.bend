import Base
import ./rules.bend as Rules
import ./proof_tree.bend as ProofTree
import ./clocked_step.bend as Step
import ./squares.bend as Squares
import ./path_tree.bend as PathTree
import ./clocked_index.bend as ClockedIndex
import ./encoding.bend as Encoding

# A deliberately simple proof target: write one clock-aware Bellman value at
# each of the 2^19 encoded slots. The proof can induct over `fuel` and use the
# existing symbolic index/decode and persistent-tree laws. This is not yet the
# entry-point generator; the old generator remains intact while refinement is
# established.
def write_slot(+kind: U32, +clock: Nat,
  +squares: List<&2, U32>,
  +next: ProofTree.Tree, +reset: ProofTree.Tree,
  +queen: ProofTree.Tree, +rook: ProofTree.Tree,
  +index: U32, tree: ProofTree.Tree) ->
  ProofTree.Tree:
  +state = Rules.decode(index)
  value = Bool.pick(U32,
    Step.value(kind, clock, state, squares,
      next, reset, queen, rook), 1, 0)
  ProofTree.set_index(tree, index, value)

def step.go(fuel: Nat, +index: U32,
  +kind: U32, +clock: Nat,
  +squares: List<&2, U32>,
  +next: ProofTree.Tree, +reset: ProofTree.Tree,
  +queen: ProofTree.Tree, +rook: ProofTree.Tree,
  tree: ProofTree.Tree) -> ProofTree.Tree:
  match fuel:
    case 0n:
      tree
    case 1n+rest:
      updated = write_slot(kind, clock, squares,
        next, reset, queen, rook, index, tree)
      step.go(rest, (index + 1 : U32), kind,
        clock, squares, next, reset, queen, rook,
        updated)

def step(+kind: U32, +clock: Nat,
  +next: ProofTree.Tree, +reset: ProofTree.Tree,
  +queen: ProofTree.Tree, +rook: ProofTree.Tree) ->
  ProofTree.Tree:
  step.go(524288n, 0, kind, clock,
    Squares.all6(), next, reset, queen, rook,
    ProofTree.filled(19n, 0))

# Tree-shaped alternative to the sequential writer. `path_index` follows the
# same most-significant-bit-first branching order as ProofTree.get; its lookup
# theorem is a direct induction on the path, with no overwritten-slot case.
def path_index(n: Nat, +prefix: U32,
  bits: Word(n)) -> U32:
  match n bits:
    case 0n WNil{}:
      prefix
    case 1n++rest WCon{False{}, tail}:
      path_index(rest, prefix, tail)
    case 1n++rest WCon{True{}, tail}:
      path_index(rest,
        (prefix + U32.shln(1, rest) : U32), tail)

def tabulate.go(n: Nat, +prefix: U32,
  +kind: U32, +clock: Nat,
  +squares: List<&2, U32>,
  +next: ProofTree.Tree, +reset: ProofTree.Tree,
  +queen: ProofTree.Tree, +rook: ProofTree.Tree) ->
  ProofTree.Tree:
  match n:
    case 0n:
      ProofTree.Leaf{Bool.pick(U32,
        Step.value(kind, clock,
          Rules.decode(prefix), squares,
          next, reset, queen, rook), 1, 0)}
    case 1n++rest:
      ProofTree.Node{
        tabulate.go(rest, prefix, kind, clock,
          squares, next, reset, queen, rook),
        tabulate.go(rest,
          (prefix + U32.shln(1, rest) : U32),
          kind, clock, squares, next,
          reset, queen, rook)}

def tabulate(+kind: U32, +clock: Nat,
  +squares: List<&2, U32>,
  +next: ProofTree.Tree, +reset: ProofTree.Tree,
  +queen: ProofTree.Tree, +rook: ProofTree.Tree) ->
  ProofTree.Tree:
  tabulate.go(19n, 0, kind, clock, squares,
    next, reset, queen, rook)

# This variant tabulates a tree of explicit 19-bit paths. Its leaf index is
# the low-first reverse of the path, zero-extended to U32. The path-tree
# induction proves every leaf corresponds to its lookup path; no arithmetic
# about a sequential index loop is needed.
def value_at_path(+kind: U32, +clock: Nat,
  +squares: List<&2, U32>,
  +next: ProofTree.Tree, +reset: ProofTree.Tree,
  +queen: ProofTree.Tree, +rook: ProofTree.Tree,
  path: Word(19n)) -> U32:
  +index = {U32{Encoding.append(13n, 19n,
    ClockedIndex.reverse(19n, path),
    Word.zero(13n))} : U32}
  Bool.pick(U32,
    Step.value(kind, clock, Rules.decode(index),
      squares, next, reset, queen, rook), 1, 0)

def from_paths(tree: PathTree.Tree<Word(19n)>,
  +kind: U32, +clock: Nat,
  +squares: List<&2, U32>,
  +next: ProofTree.Tree, +reset: ProofTree.Tree,
  +queen: ProofTree.Tree, +rook: ProofTree.Tree) ->
  ProofTree.Tree:
  match tree:
    case PathTree.Leaf{path}:
      ProofTree.Leaf{value_at_path(kind, clock,
        squares, next, reset, queen, rook, path)}
    case PathTree.Node{left, right}:
      ProofTree.Node{
        from_paths(left, kind, clock, squares,
          next, reset, queen, rook),
        from_paths(right, kind, clock, squares,
          next, reset, queen, rook)}

def tabulate_paths(+kind: U32, +clock: Nat,
  +squares: List<&2, U32>,
  +next: ProofTree.Tree, +reset: ProofTree.Tree,
  +queen: ProofTree.Tree, +rook: ProofTree.Tree) ->
  ProofTree.Tree:
  from_paths(PathTree.paths(19n), kind, clock,
    squares, next, reset, queen, rook)

# Non-pawn classes cannot reset the halfmove clock. The recursion first builds
# the table one clock later, then uses it to build the current clock. At 100,
# only an already-delivered mate can be a win.
def nonpawn.go(remaining: Nat, +clock: Nat,
  +kind: U32, +squares: List<&2, U32>,
  +paths: PathTree.Tree<Word(19n)>,
  +zero: ProofTree.Tree) -> ProofTree.Tree:
  match remaining:
    case 0n:
      from_paths(paths, kind, clock,
        squares, zero, zero, zero, zero)
    case 1n+rest:
      +next = nonpawn.go(rest, 1n+clock,
        kind, squares, paths, zero)
      from_paths(paths, kind, clock,
        squares, next, zero, zero, zero)

def nonpawn(kind: U32) -> ProofTree.Tree:
  nonpawn.go(100n, 0n, kind, Squares.all6(),
    PathTree.paths(19n),
    ProofTree.filled(19n, 0))

# A pawn push consumes one budget token and resets the halfmove clock. The
# previous-budget clock-zero table is therefore a dependency of every layer
# at the current budget. Queen and rook promotion targets are solved first.
def pawn.clock.go(remaining: Nat, +clock: Nat,
  +squares: List<&2, U32>,
  +paths: PathTree.Tree<Word(19n)>,
  +reset: ProofTree.Tree,
  +queen: ProofTree.Tree,
  +rook: ProofTree.Tree,
  +zero: ProofTree.Tree) -> ProofTree.Tree:
  match remaining:
    case 0n:
      from_paths(paths, 4, clock, squares,
        zero, reset, queen, rook)
    case 1n+rest:
      +next = pawn.clock.go(rest,
        1n+clock, squares, paths,
        reset, queen, rook, zero)
      from_paths(paths, 4, clock, squares,
        next, reset, queen, rook)

def zero_from_paths(paths: PathTree.Tree<Word(19n)>) ->
  ProofTree.Tree:
  match paths:
    case PathTree.Leaf{path}:
      ProofTree.Leaf{0}
    case PathTree.Node{left, right}:
      ProofTree.Node{
        zero_from_paths(left),
        zero_from_paths(right)}

def pawn.budget.go(pushes: Nat,
  +squares: List<&2, U32>,
  +paths: PathTree.Tree<Word(19n)>,
  +queen: ProofTree.Tree,
  +rook: ProofTree.Tree,
  +zero: ProofTree.Tree) -> ProofTree.Tree:
  match pushes:
    case 0n:
      zero_from_paths(paths)
    case 1n+rest:
      +reset = pawn.budget.go(rest,
        squares, paths, queen, rook,
        zero)
      pawn.clock.go(100n, 0n,
        squares, paths, reset,
        queen, rook, zero)

def pawn(queen: ProofTree.Tree,
  rook: ProofTree.Tree) -> ProofTree.Tree:
  pawn.budget.go(7n, Squares.all6(),
    PathTree.paths(19n), queen, rook,
    ProofTree.filled(19n, 0))
