import Base
import ./game.bend as Game
import ./pawnless_chess.bend as Chess
import ./pawnless_index.bend as Index
import ./finite_table.bend as Finite
import ./table_engine.bend as Engine
import ./clock_solver.bend as Solver

def values(states: List<&2, Chess.State>, +width: Nat,
  +table: Finite.Table(width, Game.Outcome)) -> List<&2, Game.Outcome>:
  match states:
    case Nil{}:
      Nil{}
    case Chess.KingsOnly{} <> tail:
      Game.Draw{} <> values(tail, width, table)
    case Chess.Three{board} <> tail:
      Finite.get(width, Game.Outcome, Index.encode_at(width, board), table) <> values(tail, width, table)

def fold(rest: List<&2, Game.Outcome>, +turn: Game.Player, first: Game.Outcome) -> Game.Outcome:
  Engine.fold(rest, turn, first)

def combine(view: Chess.View, outcomes: List<&2, Game.Outcome>) -> Game.Outcome:
  match view outcomes:
    case Chess.Stop{outcome} _:
      outcome
    case Chess.Play{turn, children} Nil{}:
      Game.Draw{}
    case Chess.Play{turn, children} head <> tail:
      fold(tail, turn, head)

def base(+width: Nat, material: Chess.Material, key: Word(width)) -> Game.Outcome:
  Game.evaluate(Chess.boundary(Chess.view(material, Chess.Three{Index.decode_at(width, key)})))

def at(+width: Nat, material: Chess.Material, previous: Finite.Table(width, Game.Outcome), board: Chess.Board) -> Game.Outcome:
  +node = Chess.view(material, Chess.Three{board})
  combine(node, values(Chess.children(node), width, previous))

# Compile the component once. Reversible moves keep their table key; every
# capture in this domain enters bare kings, whose completed result is Draw.
def edges(states: List<&2, Chess.State>, +width: Nat) -> List<&2, Solver.Edge<width>>:
  match states:
    case Nil{}:
      Nil{}
    case Chess.KingsOnly{} <> tail:
      Solver.Reset{Game.Draw{}} <> edges(tail, width)
    case Chess.Three{board} <> tail:
      Solver.Quiet{Index.encode_at(width, board)} <> edges(tail, width)

def node(+width: Nat, view: Chess.View) -> Solver.Node<width>:
  match view:
    case Chess.Stop{result}:
      Solver.Terminal{result}
    case Chess.Play{turn, children}:
      Solver.Choice{turn, edges(children, width)}

def graph_fill(depth: Nat, +width: Nat, +material: Chess.Material,
  keys: Finite.Table(depth, Word(width))) -> Finite.Table(depth, Solver.Node<width>):
  match depth keys:
    case 0n key:
      node(width, Chess.view(material, Chess.Three{Index.decode_at(width, key)}))
    case 1n++rest Finite.Fork{left, right}:
      a b = graph_fill(rest, width, material, left) graph_fill(rest, width, material, right)
      Finite.Fork{a, b}

def graph(+width: Nat, material: Chess.Material) -> Finite.Table(width, Solver.Node<width>):
  graph_fill(width, width, material, Finite.keys(width))

def generate(remaining: Nat, +width: Nat, material: Chess.Material) -> Finite.Table(width, Game.Outcome):
  Solver.generate(remaining, width, graph(width, material))

# Compatibility projections shared by the existing serialization proofs.
def bytes(depth: Nat, table: Finite.Table(depth, Game.Outcome)) -> Finite.Table(depth, U32):
  Engine.bytes(depth, table)

def file(remaining: Nat, +width: Nat, material: Chess.Material) -> List<&2, U32>:
  Finite.flatten(width, bytes(width, generate(remaining, width, material)))
