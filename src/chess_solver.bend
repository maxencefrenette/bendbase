import Base
import ./position.bend as P
import ./position_index.bend as Index
import ./position_address.bend as Address
import ./chess.bend as Chess
import ./chess_graph.bend as Graph
import ./chess_cache.bend as Cache
import ./chess_measure.bend as Measure
import ./component_cache.bend as Stages
import ./material_directory.bend as Directory
import ./material_cache.bend as Registry
import ./table_cache.bend as Tables
import ./clock_solver.bend as Solver
import ./finite_table.bend as Finite
import ./game.bend as Game

# Exact-width conversion: never truncate or zero-pad a quiet destination.
def put_bit(-width: Nat, bit: Bool, tail: Maybe<&2, Word(width)>) -> Maybe<&2, Word(1n+width)>:
  match tail:
    case None{}:
      None{}
    case Some{word}:
      Some{WCon{bit, word}}

def key(source: Nat, target: Nat, word: Word(source)) -> Maybe<&2, Word(target)>:
  match source target word:
    case 0n 0n WNil{}:
      Some{WNil{}}
    case 0n 1n+rest WNil{}:
      None{}
    case 1n+rest 0n word:
      None{}
    case 1n+rest 1n+more WCon{bit, tail}:
      put_bit(more, bit, key(rest, more, tail))

def quiet(-width: Nat, key: Maybe<&2, Word(width)>) -> Maybe<&2, Solver.Edge<width>>:
  match key:
    case None{}:
      None{}
    case Some{word}:
      Some{Solver.Quiet{word}}

def edge(+width: Nat, stages: List<&2, Stages.Stage>, edge: Graph.Edge) -> Maybe<&2, Solver.Edge<width>>:
  match edge:
    case Graph.Quiet{Address.Address{n, material, word}}:
      quiet(width, key(Index.width(n), width, word))
    case Graph.Reset{address}:
      Cache.reset(width, stages, address)

def cons(-width: Nat, head: Maybe<&2, Solver.Edge<width>>, tail: Maybe<&2, List<&2, Solver.Edge<width>>>) -> Maybe<&2, List<&2, Solver.Edge<width>>>:
  match head tail:
    case Some{head} Some{tail}:
      Some{head <> tail}
    case _ _:
      None{}

def edges(+width: Nat, +stages: List<&2, Stages.Stage>, children: List<&2, Graph.Edge>) -> Maybe<&2, List<&2, Solver.Edge<width>>>:
  match children:
    case Nil{}:
      Some{Nil{}}
    case head <> tail:
      cons(width, edge(width, stages, head), edges(width, stages, tail))

def choice(-width: Nat, turn: Game.Player, edges: Maybe<&2, List<&2, Solver.Edge<width>>>) -> Maybe<&2, Solver.Node<width>>:
  match edges:
    case None{}:
      None{}
    case Some{children}:
      Some{Solver.Choice{turn, children}}

def node(+width: Nat, stages: List<&2, Stages.Stage>, node: Graph.Node) -> Maybe<&2, Solver.Node<width>>:
  match node:
    case Graph.Terminal{result}:
      Some{Solver.Terminal{result}}
    case Graph.Choice{turn, children}:
      choice(width, turn, edges(width, stages, children))

def material(name: List<&2, P.Descriptor>) -> P.Material(List.length(&2, P.Descriptor, name)):
  match name:
    case Nil{}:
      Unit{}
    case head <> tail:
      P.MaterialCell{head, material(tail)}

# Off-stage slots are padding, not claims about their chess outcome. Quiet
# closure keeps all queried continuations in the component's own stage.
def entry_live(+width: Nat, live: Bool, stages: List<&2, Stages.Stage>, anchor: Game.Player, board: P.Position) -> Maybe<&2, Solver.Node<width>>:
  match live:
    case False{}:
      Some{Solver.Terminal{Game.Draw{}}}
    case True{}:
      node(width, stages, Graph.node(14n, anchor, board))

def entry(+name: List<&2, P.Descriptor>, +stage: Nat, stages: List<&2, Stages.Stage>, key: Word(Directory.width(name))) -> Maybe<&2, Solver.Node<Directory.width(name)>>:
  +n = List.length(&2, P.Descriptor, name)
  +board = Index.decode(n, key)
  +position = P.position(n, material(name), board)
  entry_live(Directory.width(name), Stages.equal(Measure.position(position), stage), stages, P.anchor(P.frame(n, board)), position)

def fork(-depth: Nat, -width: Nat, left: Maybe<&2, Finite.Table(depth, Solver.Node<width>)>, right: Maybe<&2, Finite.Table(depth, Solver.Node<width>)>) ->
  Maybe<&2, Finite.Table(1n+depth, Solver.Node<width>)>:
  match left right:
    case Some{left} Some{right}:
      Some{Finite.Fork{left, right}}
    case _ _:
      None{}

def fill(depth: Nat, +name: List<&2, P.Descriptor>, +stage: Nat, +stages: List<&2, Stages.Stage>, keys: Finite.Table(depth, Word(Directory.width(name)))) ->
  Maybe<&2, Finite.Table(depth, Solver.Node<Directory.width(name)>)>:
  match depth keys:
    case 0n key:
      entry(name, stage, stages, key)
    case 1n++rest Finite.Fork{left, right}:
      a b = fill(rest, name, stage, stages, left) fill(rest, name, stage, stages, right)
      fork(rest, Directory.width(name), a, b)

def graph(+name: List<&2, P.Descriptor>, stage: Nat, stages: List<&2, Stages.Stage>) -> Maybe<&2, Finite.Table(Directory.width(name), Solver.Node<Directory.width(name)>)>:
  fill(Directory.width(name), name, stage, stages, Finite.keys(Directory.width(name)))

def solve(remaining: Nat, +width: Nat, graph: Maybe<&2, Finite.Table(width, Solver.Node<width>)>) -> Maybe<&2, Finite.Table(width, Game.Outcome)>:
  match graph:
    case None{}:
      None{}
    case Some{nodes}:
      Some{Solver.generate(remaining, width, nodes)}

def component(+name: List<&2, P.Descriptor>, stage: Nat, limit: Nat, stages: List<&2, Stages.Stage>) -> Maybe<&2, Finite.Table(Directory.width(name), Game.Outcome)>:
  solve(limit, Directory.width(name), graph(name, stage, stages))

def named(+name: List<&2, P.Descriptor>, table: Maybe<&2, Finite.Table(Directory.width(name), Game.Outcome)>, tail: Maybe<&2, List<&2, Registry.Named>>) -> Maybe<&2, List<&2, Registry.Named>>:
  match table tail:
    case Some{table} Some{tail}:
      Some{Registry.Named{name, Tables.Entry{Directory.width(name), table}} <> tail}
    case _ _:
      None{}

def directory(names: List<&2, List<&2, P.Descriptor>>, +stage: Nat, +limit: Nat, +stages: List<&2, Stages.Stage>) -> Maybe<&2, List<&2, Registry.Named>>:
  match names:
    case Nil{}:
      Some{Nil{}}
    case +name <> tail:
      named(name, component(name, stage, limit, stages), directory(tail, stage, limit, stages))

def completed(stage: Nat, entries: Maybe<&2, List<&2, Registry.Named>>, previous: List<&2, Stages.Stage>) -> Maybe<&2, List<&2, Stages.Stage>>:
  match entries:
    case None{}:
      None{}
    case Some{entries}:
      Some{Stages.Stage{stage, entries} <> previous}

def next(+stage: Nat, capacity: Nat, limit: Nat, previous: Maybe<&2, List<&2, Stages.Stage>>) -> Maybe<&2, List<&2, Stages.Stage>>:
  match previous:
    case None{}:
      None{}
    case Some{+stages}:
      completed(stage, directory(Directory.names(capacity), stage, limit, stages), stages)

# Experimental cached pipeline for all material sizes; no legacy dispatch.
# Compiler completeness and semantic cache induction remain proof obligations
# for this alternative, not for chess_tables' proved direct generator.
# Failure is never converted to an outcome or a partial table.
def generate(count: Nat, +capacity: Nat, +limit: Nat) -> Maybe<&2, List<&2, Stages.Stage>>:
  match count:
    case 0n:
      Some{Nil{}}
    case 1n++prior:
      next(1n+prior, capacity, limit, generate(prior, capacity, limit))
