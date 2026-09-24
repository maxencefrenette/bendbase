import Base
import ./game.bend as Game
import ./finite_table.bend as Finite
import ./table_engine.bend as Engine
import ./pawnless_chess.bend as Three

# A reversible component has one key space, of arbitrary width. Captures,
# pawn advances and promotions leave it and consult completed dependencies.
# There are deliberately no material-family cases in this solver.
type Edge<-width: Nat> is Data:
  Quiet{key: Word(width)}
  Reset{result: Game.Outcome}

type Node<-width: Nat> is Data:
  Terminal{result: Game.Outcome}
  Choice{turn: Game.Player, children: List<&2, Edge<width>>}

def boundary(-width: Nat, node: Node<width>) -> Game.Outcome:
  match node:
    case Terminal{result}:
      result
    case Choice{turn, children}:
      Game.Draw{}

def edge_value(+width: Nat, edge: Edge<width>, previous: Finite.Table(width, Game.Outcome)) -> Game.Outcome:
  match edge:
    case Quiet{key}:
      Finite.get(width, Game.Outcome, key, previous)
    case Reset{result}:
      result

def values(+width: Nat, children: List<&2, Edge<width>>,
  +previous: Finite.Table(width, Game.Outcome)) -> List<&2, Game.Outcome>:
  match children:
    case Nil{}:
      Nil{}
    case head <> tail:
      edge_value(width, head, previous) <> values(width, tail, previous)

def combine(-width: Nat, node: Node<width>, values: List<&2, Game.Outcome>) -> Game.Outcome:
  match node values:
    case Terminal{result} _:
      result
    case Choice{turn, children} Nil{}:
      Game.Draw{}
    case Choice{turn, children} head <> tail:
      Engine.fold(tail, turn, head)

def children(-width: Nat, node: Node<width>) -> List<&2, Edge<width>>:
  match node:
    case Terminal{result}:
      Nil{}
    case Choice{turn, children}:
      children

type Layer<-width: Nat> is Data:
  Initial{}
  Next{previous: Finite.Table(width, Game.Outcome)}

def at(+width: Nat, layer: Layer<width>, +node: Node<width>) -> Game.Outcome:
  match layer:
    case Initial{}:
      boundary(width, node)
    case Next{previous}:
      combine(width, node, values(width, children(width, node), previous))

type Context<-width: Nat> is Data:
  Context{graph: Finite.Table(width, Node<width>), layer: Layer<width>}

def Family(width: Nat, low: Nat) -> Data:
  Context<width>

def entry(+width: Nat, +low: Nat, context: Context<width>, key: Word(width)) -> Game.Outcome:
  match context:
    case Context{graph, layer}:
      at(width, layer, Finite.get(width, Node<width>, key, graph))

def layer(+width: Nat, graph: Finite.Table(width, Node<width>), phase: Layer<width>) -> Finite.Table(width, Game.Outcome):
  Engine.fill(~Family, ~entry, width, width, 0n, Context{graph, phase}, Finite.keys(width))

def generate(remaining: Nat, +width: Nat, +graph: Finite.Table(width, Node<width>)) -> Finite.Table(width, Game.Outcome):
  match remaining:
    case 0n:
      layer(width, graph, Initial{})
    case 1n+rest:
      layer(width, graph, Next{generate(rest, width, graph)})

# Independent game-tree unfolding for the component proof. Reset endpoints
# summarize completed games; chess integration must prove those summaries and
# that every resetting edge points to an earlier dependency (not a quiet edge).
def assemble(-width: Nat, node: Node<width>, trees: List<&2, Game.Tree>) -> Game.Tree:
  match node trees:
    case Terminal{result} _:
      Game.End{result}
    case Choice{turn, children} Nil{}:
      Game.End{Game.Draw{}}
    case Choice{turn, children} head <> tail:
      Three.choices(tail, turn, head)

def forest(remaining: Nat, +width: Nat, edges: List<&2, Edge<width>>,
  +graph: Finite.Table(width, Node<width>)) -> List<&2, Game.Tree>:
  match remaining edges:
    case 0n Nil{}:
      Nil{}
    case 1n+rest Nil{}:
      Nil{}
    case 0n Reset{result} <> tail:
      Game.End{result} <> forest(0n, width, tail, graph)
    case 1n++rest Reset{result} <> tail:
      Game.End{result} <> forest(1n+rest, width, tail, graph)
    case 0n Quiet{key} <> tail:
      Game.End{boundary(width, Finite.get(width, Node<width>, key, graph))} <> forest(0n, width, tail, graph)
    case 1n++rest Quiet{key} <> tail:
      +node = Finite.get(width, Node<width>, key, graph)
      assemble(width, node, forest(rest, width, children(width, node), graph)) <> forest(1n+rest, width, tail, graph)

def tree(remaining: Nat, +width: Nat, graph: Finite.Table(width, Node<width>), key: Word(width)) -> Game.Tree:
  Three.only(forest(remaining, width, Quiet{key} <> Nil{}, graph))

def file(remaining: Nat, +width: Nat, graph: Finite.Table(width, Node<width>)) -> List<&2, U32>:
  Finite.flatten(width, Engine.bytes(width, generate(remaining, width, graph)))
