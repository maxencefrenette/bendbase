import Base
import ./material_cache.bend as Registry
import ./table_cache.bend as Cache
import ./game.bend as Game
import ./pawnless_chess.bend as Three
import ./pawnless_index.bend as Index
import ./four_index.bend as FourIndex
import ./material_chess.bend as Chess
import ./four_chess.bend as Rules
import ./finite_table.bend as Finite
import ./table_engine.bend as Engine
import ./clock_solver.bend as Solver
import ./dependency_engine.bend as Dependencies
import ./material_catalog.bend as Catalog

# Clock-layer dynamic programming over the SAME generalized move rules as
# the chess semantics. No recursive game evaluation occurs in a layer.
type Scope is Data:
  Single{kind: Three.Material}
  Double{material: FourIndex.Material}

def decode(+width: Nat, scope: Scope, key: Word(width)) -> Chess.Position:
  match scope:
    case Single{kind}:
      Chess.from_three(kind, Index.decode_at(width, key))
    case Double{material}:
      FourIndex.position(material, FourIndex.decode_at(width, key))

def lower_value(+width: Nat, lower: Maybe<&2, List<&2, Registry.Named>>, kind: Three.Material, board: Three.Board) -> Game.Outcome:
  match lower:
    case None{}:
      Game.Draw{}
    case Some{bundle}:
      Cache.value(Registry.lookup(bundle, Catalog.signature(kind), width, Index.encode_at(width, board)), Game.Draw{})

def edge(+width: Nat, +low: Nat, scope: Scope, lower: Maybe<&2, List<&2, Registry.Named>>, position: Chess.Position) -> Solver.Edge<width>:
  match scope position:
    case Single{kind} Chess.Position{turn, wk, bk, Chess.Man{owner, actual, pc} <> Nil{}}:
      Solver.Quiet{Index.encode_at(width, Three.Board{owner, turn, wk, bk, pc})}
    case Double{material} Chess.Position{turn, wk, bk, Chess.Man{owner, kind, pc} <> Nil{}}:
      Solver.Reset{lower_value(low, lower, kind, Three.Board{owner, turn, wk, bk, pc})}
    case Double{material} Chess.Position{turn, wk, bk, Chess.Man{owner, first, pc} <> Chess.Man{other, second, at} <> Nil{}}:
      Solver.Quiet{FourIndex.encode_at(width, FourIndex.Board{Three.Board{owner, turn, wk, bk, pc}, at})}
    case _ _:
      Solver.Reset{Game.Draw{}}

def lookup(+width: Nat, +low: Nat, scope: Scope, previous: Finite.Table(width, Game.Outcome),
  lower: Maybe<&2, List<&2, Registry.Named>>, position: Chess.Position) -> Game.Outcome:
  Solver.edge_value(width, edge(width, low, scope, lower, position), previous)

def values(positions: List<&2, Chess.Position>, +width: Nat, +low: Nat, +scope: Scope,
  +previous: Finite.Table(width, Game.Outcome), +lower: Maybe<&2, List<&2, Registry.Named>>) -> List<&2, Game.Outcome>:
  match positions:
    case Nil{}:
      Nil{}
    case head <> tail:
      lookup(width, low, scope, previous, lower, head) <> values(tail, width, low, scope, previous, lower)

def combine(view: Rules.View, values: List<&2, Game.Outcome>) -> Game.Outcome:
  match view values:
    case Rules.Stop{result} _:
      result
    case Rules.Play{turn, children} Nil{}:
      Game.Draw{}
    case Rules.Play{turn, children} head <> tail:
      Engine.fold(tail, turn, head)

def at(+width: Nat, +low: Nat, +scope: Scope, layer: Solver.Layer<width>, lower: Maybe<&2, List<&2, Registry.Named>>,
  moves: Nat, position: Chess.Position) -> Game.Outcome:
  match layer:
    case Solver.Initial{}:
      Game.evaluate(Rules.boundary(Rules.view(moves, position)))
    case Solver.Next{previous}:
      +node = Rules.view(moves, position)
      combine(node, values(Rules.children(node), width, low, scope, previous, lower))

def edges(positions: List<&2, Chess.Position>, +width: Nat, +low: Nat, +scope: Scope,
  +lower: Maybe<&2, List<&2, Registry.Named>>) -> List<&2, Solver.Edge<width>>:
  match positions:
    case Nil{}:
      Nil{}
    case head <> tail:
      edge(width, low, scope, lower, head) <> edges(tail, width, low, scope, lower)

def node(+width: Nat, low: Nat, scope: Scope, lower: Maybe<&2, List<&2, Registry.Named>>, view: Rules.View) -> Solver.Node<width>:
  match view:
    case Rules.Stop{result}:
      Solver.Terminal{result}
    case Rules.Play{turn, positions}:
      Solver.Choice{turn, edges(positions, width, low, scope, lower)}

def graph_fill(depth: Nat, +width: Nat, +low: Nat, +scope: Scope, +moves: Nat,
  +lower: Maybe<&2, List<&2, Registry.Named>>, keys: Finite.Table(depth, Word(width))) -> Finite.Table(depth, Solver.Node<width>):
  match depth keys:
    case 0n key:
      node(width, low, scope, lower, Rules.view(moves, decode(width, scope, key)))
    case 1n++rest Finite.Fork{left, right}:
      a b = graph_fill(rest, width, low, scope, moves, lower, left) graph_fill(rest, width, low, scope, moves, lower, right)
      Finite.Fork{a, b}

def graph(+width: Nat, low: Nat, scope: Scope, moves: Nat, lower: Maybe<&2, List<&2, Registry.Named>>) -> Finite.Table(width, Solver.Node<width>):
  graph_fill(width, width, low, scope, moves, lower, Finite.keys(width))

def generate(remaining: Nat, +width: Nat, low: Nat, scope: Scope, moves: Nat,
  lower: Maybe<&2, List<&2, Registry.Named>>) -> Finite.Table(width, Game.Outcome):
  Solver.generate(remaining, width, graph(width, low, scope, moves, lower))

def phase(remaining: Nat, +width: Nat, +low: Nat, +scope: Scope, +moves: Nat,
  +lower: Maybe<&2, List<&2, Registry.Named>>) -> Solver.Layer<width>:
  match remaining:
    case 0n:
      Solver.Initial{}
    case 1n+rest:
      Solver.Next{generate(rest, width, low, scope, moves, lower)}

type FamilyContext is Data:
  FamilyContext{limit: Nat, moves: Nat}

def Family(width: Nat) -> Data:
  FamilyContext

def single_entry(+width: Nat, context: Family(width), kind: Three.Material) -> Cache.Entry:
  match context:
    case FamilyContext{limit, moves}:
      Cache.Entry{width, generate(limit, width, width, Single{kind}, moves, None{})}

def singles(limit: Nat, +width: Nat, moves: Nat) -> List<&2, Registry.Named>:
  Catalog.named(Dependencies.family(~Three.Material, ~Family, ~Cache.Family, ~single_entry, 2n, width, FamilyContext{limit, moves}, Catalog.pieces()))

def four(+limit: Nat, width: Nat, +low: Nat, +moves: Nat, material: FourIndex.Material) -> Finite.Table(width, Game.Outcome):
  generate(limit, width, low, Double{material}, moves, Some{singles(limit, low, moves)})

def file_with(limit: Nat, +width: Nat, low: Nat, moves: Nat, material: FourIndex.Material, lower: List<&2, Registry.Named>) -> List<&2, U32>:
  Finite.flatten(width, Engine.bytes(width, generate(limit, width, low, Double{material}, moves, Some{lower})))

def file(+limit: Nat, +width: Nat, +low: Nat, +moves: Nat, material: FourIndex.Material) -> List<&2, U32>:
  file_with(limit, width, low, moves, material, singles(limit, low, moves))
