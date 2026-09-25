import Base
import ./game.bend as Game
import ./position.bend as P
import ./position_address.bend as Address
import ./chess.bend as Chess
import ./chess_graph.bend as Graph
import ./chess_measure.bend as Measure
import ./pawnless_chess.bend as Choices

# Chess semantics, not a second table generator: this unfolds legal play into
# the existing strategy-based Game.Tree. No cache, table, or compiled solver
# is consulted. Castling is absent everywhere; EP remains part of Position.
type State is Data:
  State{remaining: Nat, position: P.Position}

def children(node: Graph.Node) -> List<&2, Graph.Edge>:
  match node:
    case Graph.Terminal{result}:
      Nil{}
    case Graph.Choice{turn, children}:
      children

def states(+limit: Nat, +remaining: Nat, edges: List<&2, Graph.Edge>) -> List<&2, State>:
  match edges:
    case Nil{}:
      Nil{}
    case +edge <> tail:
      State{Graph.next_clock(limit, remaining, edge), Address.position(Graph.address(edge))} <> states(limit, remaining, tail)

def assemble(node: Graph.Node, trees: List<&2, Game.Tree>) -> Game.Tree:
  match node trees:
    case Graph.Terminal{result} _:
      Game.End{result}
    case Graph.Choice{turn, edges} Nil{}:
      Game.End{Game.Draw{}}
    case Graph.Choice{turn, edges} head <> tail:
      Choices.choices(tail, turn, head)

def forest(fuel: Nat, items: List<&2, State>, +limit: Nat, +actions: Nat) -> List<&2, Game.Tree>:
  match fuel items:
    case _ Nil{}:
      Nil{}
    case 0n State{remaining, +position} <> tail:
      Game.End{Chess.boundary(Chess.view(actions, position))} <> forest(0n, tail, limit, actions)
    case 1n++prior State{0n, +position} <> tail:
      Game.End{Chess.boundary(Chess.view(actions, position))} <> forest(1n+prior, tail, limit, actions)
    case 1n++prior State{1n+clock, +position} <> tail:
      +node = Graph.node(actions, Game.White{}, position)
      assemble(node, forest(prior, states(limit, 1n+clock, children(node)), limit, actions)) <> forest(1n+prior, tail, limit, actions)

def tree(+limit: Nat, +remaining: Nat, +position: P.Position) -> Game.Tree:
  Choices.only(forest(Measure.budget(limit, Measure.position(position), remaining), [State{remaining, position}], limit, 14n))

# Semantic observation used to justify sharing continuations: each child is
# unfolded independently, with its own sufficient budget.
def standalone(items: List<&2, State>, +limit: Nat) -> List<&2, Game.Tree>:
  match items:
    case Nil{}:
      Nil{}
    case State{remaining, position} <> tail:
      tree(limit, remaining, position) <> standalone(tail, limit)

def wdl(position: P.Position) -> Game.Outcome:
  Game.evaluate(tree(100n, 100n, position))

# A legal line deliberately overapproximates continuations: it even allows
# moves after insufficient-material detection. A bound for this larger set
# therefore also bounds paths in the terminal-pruned game tree.
def Line(moves: List<&2, Chess.Action>, +limit: Nat, remaining: Nat, +position: P.Position) -> Type:
  match moves remaining:
    case Nil{} _:
      Unit
    case head <> tail 0n:
      Empty
    case +head <> tail 1n+clock:
      Game.Truth(Chess.legal(position, head)) &
        Line(tail, limit, Bool.pick(Nat, Chess.resets(position, head), limit, clock), Chess.after(position, head))

# Structural statement that NO fuel-exhaustion branch is used anywhere in
# the unfolding. Clock exhaustion is allowed and retains terminal precedence.
def NoCutoff(fuel: Nat, items: List<&2, State>, +limit: Nat, +actions: Nat) -> Type:
  match fuel items:
    case _ Nil{}:
      Unit
    case 0n head <> tail:
      Empty
    case 1n++prior State{0n, position} <> tail:
      NoCutoff(1n+prior, tail, limit, actions)
    case 1n++prior State{1n+clock, +position} <> tail:
      NoCutoff(prior, states(limit, 1n+clock, children(Graph.node(actions, Game.White{}, position))), limit, actions) &
        NoCutoff(1n+prior, tail, limit, actions)
