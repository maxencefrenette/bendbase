import Base
import ./game.bend as Game
import ./position.bend as P
import ./position_address.bend as Address
import ./chess.bend as Chess
import ./pawnless_chess.bend as Three
import ./finite_table.bend as Finite

# Unresolved edges retain full addresses, not presumed WDL outcomes. Missing
# dependencies must not silently become draws. Resolution into clock_solver
# nodes is a separate, proof-obligated scheduling step.
type Edge is Data:
  Quiet{address: Address.Address}
  Reset{address: Address.Address}

def edge(reset: Bool, address: Address.Address) -> Edge:
  match reset:
    case False{}:
      Quiet{address}
    case True{}:
      Reset{address}

def route(anchor: Game.Player, +position: P.Position, +move: Chess.Action) -> Edge:
  edge(Chess.resets(position, move), Address.of_position(anchor, Chess.after(position, move)))

def address(edge: Edge) -> Address.Address:
  match edge:
    case Quiet{address}:
      address
    case Reset{address}:
      address

def resets(edge: Edge) -> Bool:
  match edge:
    case Quiet{address}:
      False{}
    case Reset{address}:
      True{}

def next_clock(limit: Nat, remaining: Nat, edge: Edge) -> Nat:
  match edge:
    case Quiet{address}:
      Nat.sub(remaining, 1n)
    case Reset{address}:
      limit

def positions(edges: List<&2, Edge>) -> List<&2, P.Position>:
  match edges:
    case Nil{}:
      Nil{}
    case head <> tail:
      Address.position(address(head)) <> positions(tail)

def include(allowed: Bool, next: Edge, tail: List<&2, Edge>) -> List<&2, Edge>:
  match allowed:
    case True{}:
      next <> tail
    case False{}:
      tail

def scan(depth: Nat, +width: Nat, +anchor: Game.Player, +position: P.Position,
  keys: Finite.Table(depth, Word(width)), tail: List<&2, Edge>) -> List<&2, Edge>:
  match depth keys:
    case 0n +key:
      include(Chess.legal(position, Chess.action_at(width, key)), route(anchor, position, Chess.action_at(width, key)), tail)
    case 1n++rest Finite.Fork{left, right}:
      scan(rest, width, anchor, position, left, scan(rest, width, anchor, position, right, tail))

def successors(+width: Nat, anchor: Game.Player, position: P.Position) -> List<&2, Edge>:
  scan(width, width, anchor, position, Finite.keys(width), Nil{})

type Node is Data:
  Terminal{result: Game.Outcome}
  Choice{turn: Game.Player, children: List<&2, Edge>}

def node.moves(+position: P.Position, edges: List<&2, Edge>) -> Node:
  match position edges:
    case P.Position{+turn, wk, bk, men, ep, target} Nil{}:
      Terminal{Three.mate(Chess.checked(position, turn), turn)}
    case P.Position{turn, wk, bk, men, ep, target} head <> tail:
      Choice{turn, head <> tail}

def node.live(live: Bool, width: Nat, anchor: Game.Player, +position: P.Position) -> Node:
  match live:
    case False{}:
      Terminal{Game.Draw{}}
    case True{}:
      node.moves(position, successors(width, anchor, position))

def node(width: Nat, anchor: Game.Player, +position: P.Position) -> Node:
  match position:
    case P.Position{turn, wk, bk, men, ep, target}:
      node.live(Chess.valid(position) && Bool.not(Chess.insufficient(men)), width, anchor, position)

def view(node: Node) -> Chess.View:
  match node:
    case Terminal{result}:
      Chess.Terminal{result}
    case Choice{turn, children}:
      Chess.Play{turn, positions(children)}
