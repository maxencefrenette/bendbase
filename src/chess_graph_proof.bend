import Base
import ./game.bend as Game
import ./position.bend as P
import ./position_address.bend as Address
import ./position_address_proof.bend as AddressProof
import ./chess.bend as Chess
import ./chess_graph.bend as Graph
import ./finite_table.bend as Finite
import ./chess_measure.bend as Measure
import ./chess_selection_proof.bend as SelectionProof

def edge_address(+reset: Bool, +address: Address.Address) ->
  {Graph.address(Graph.edge(reset, address)) == address : Address.Address}:
  match reset:
    case False{}:
      {==}
    case True{}:
      {==}

def edge_reset(+reset: Bool, +address: Address.Address) ->
  {Graph.resets(Graph.edge(reset, address)) == reset : Bool}:
  match reset:
    case False{}:
      {==}
    case True{}:
      {==}

def route_position(+anchor: Game.Player, +position: P.Position, +move: Chess.Action) ->
  {Address.position(Graph.address(Graph.route(anchor, position, move))) == Chess.after(position, move) : P.Position}:
  Equal.trans(P.Position, Address.position(Graph.address(Graph.route(anchor, position, move))),
    Address.position(Address.of_position(anchor, Chess.after(position, move))), Chess.after(position, move),
    Equal.cong(Address.Address, P.Position, address => Address.position(address),
      Graph.address(Graph.route(anchor, position, move)), Address.of_position(anchor, Chess.after(position, move)),
      edge_address(Chess.resets(position, move), Address.of_position(anchor, Chess.after(position, move)))),
    AddressProof.roundtrip(anchor, Chess.after(position, move)))

def route_reset(+anchor: Game.Player, +position: P.Position, +move: Chess.Action) ->
  {Graph.resets(Graph.route(anchor, position, move)) == Chess.resets(position, move) : Bool}:
  edge_reset(Chess.resets(position, move), Address.of_position(anchor, Chess.after(position, move)))

def clock_policy(+limit: Nat, +remaining: Nat, +reset: Bool, +address: Address.Address) ->
  {Graph.next_clock(limit, remaining, Graph.edge(reset, address)) ==
   Bool.pick(Nat, reset, limit, Nat.sub(remaining, 1n)) : Nat}:
  match reset:
    case False{}:
      {==}
    case True{}:
      {==}

def route_clock(+limit: Nat, +remaining: Nat, +anchor: Game.Player, +position: P.Position, +move: Chess.Action) ->
  {Graph.next_clock(limit, remaining, Graph.route(anchor, position, move)) ==
   Bool.pick(Nat, Chess.resets(position, move), limit, Nat.sub(remaining, 1n)) : Nat}:
  clock_policy(limit, remaining, Chess.resets(position, move), Address.of_position(anchor, Chess.after(position, move)))

def predecessor(+n: Nat) -> {Nat.sub(1n+n, 1n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+rest:
      {==}

# Full-address routing and its clock update preserve the decreasing bound.
# This is independent of material size, pawn count, promotion, and EP state.
def route_budget(+limit: Nat, +remaining: Nat, +anchor: Game.Player, +position: P.Position, +move: Chess.Action,
  legal: Game.Truth(Chess.legal(position, move))) ->
  Measure.Lt(Measure.budget(limit, Measure.position(Address.position(Graph.address(Graph.route(anchor, position, move)))),
    Graph.next_clock(limit, 1n+remaining, Graph.route(anchor, position, move))),
    Measure.budget(limit, Measure.position(position), 1n+remaining)):
  %Equal.sym(P.Position, Address.position(Graph.address(Graph.route(anchor, position, move))), Chess.after(position, move),
    route_position(anchor, position, move)) :
    Measure.Lt(Measure.budget(limit, Measure.position(_), Graph.next_clock(limit, 1n+remaining, Graph.route(anchor, position, move))),
      Measure.budget(limit, Measure.position(position), 1n+remaining))
  %Equal.sym(Nat, Graph.next_clock(limit, 1n+remaining, Graph.route(anchor, position, move)),
    Bool.pick(Nat, Chess.resets(position, move), limit, Nat.sub(1n+remaining, 1n)), route_clock(limit, 1n+remaining, anchor, position, move)) :
    Measure.Lt(Measure.budget(limit, Measure.position(Chess.after(position, move)), _), Measure.budget(limit, Measure.position(position), 1n+remaining))
  %Equal.sym(Nat, Nat.sub(1n+remaining, 1n), remaining, predecessor(remaining)) :
    Measure.Lt(Measure.budget(limit, Measure.position(Chess.after(position, move)), Bool.pick(Nat, Chess.resets(position, move), limit, _)),
      Measure.budget(limit, Measure.position(position), 1n+remaining))
  SelectionProof.legal_budget(limit, remaining, position, move, legal)

def included(+allowed: Bool, +anchor: Game.Player, +position: P.Position, +move: Chess.Action, +tail: List<&2, Graph.Edge>) ->
  {Graph.positions(Graph.include(allowed, Graph.route(anchor, position, move), tail)) ==
   Chess.include(allowed, Chess.after(position, move), Graph.positions(tail)) : List<&2, P.Position>}:
  match allowed:
    case False{}:
      {==}
    case True{}:
      Equal.cong(P.Position, List<&2, P.Position>, next => next <> Graph.positions(tail),
        Address.position(Graph.address(Graph.route(anchor, position, move))), Chess.after(position, move), route_position(anchor, position, move))

# Induction over the move-index tree, never over the position space.
def scan(depth: Nat, +width: Nat, +anchor: Game.Player, +position: P.Position,
  +keys: Finite.Table(depth, Word(width)), +tail: List<&2, Graph.Edge>) ->
  {Graph.positions(Graph.scan(depth, width, anchor, position, keys, tail)) ==
   Chess.successors.go(depth, width, position, keys, Graph.positions(tail)) : List<&2, P.Position>}:
  match depth keys:
    case 0n key:
      included(Chess.legal(position, Chess.action_at(width, key)), anchor, position, Chess.action_at(width, key), tail)
    case 1n++rest Finite.Fork{+left, +right}:
      Equal.trans(List<&2, P.Position>, Graph.positions(Graph.scan(1n+rest, width, anchor, position, keys, tail)),
        Chess.successors.go(rest, width, position, left, Graph.positions(Graph.scan(rest, width, anchor, position, right, tail))),
        Chess.successors.go(1n+rest, width, position, keys, Graph.positions(tail)),
        scan(rest, width, anchor, position, left, Graph.scan(rest, width, anchor, position, right, tail)),
        Equal.cong(List<&2, P.Position>, List<&2, P.Position>, acc => Chess.successors.go(rest, width, position, left, acc),
          Graph.positions(Graph.scan(rest, width, anchor, position, right, tail)),
          Chess.successors.go(rest, width, position, right, Graph.positions(tail)), scan(rest, width, anchor, position, right, tail)))

def successors(+width: Nat, +anchor: Game.Player, +position: P.Position) ->
  {Graph.positions(Graph.successors(width, anchor, position)) == Chess.successors(width, position) : List<&2, P.Position>}:
  scan(width, width, anchor, position, Finite.keys(width), Nil{})

def node_moves(+position: P.Position, +edges: List<&2, Graph.Edge>) ->
  {Graph.view(Graph.node.moves(position, edges)) == Chess.view.moves(position, Graph.positions(edges)) : Chess.View}:
  match position edges:
    case P.Position{turn, wk, bk, men, ep, target} Nil{}:
      {==}
    case P.Position{turn, wk, bk, men, ep, target} head <> tail:
      {==}

def node_live(+live: Bool, +width: Nat, +anchor: Game.Player, +position: P.Position) ->
  {Graph.view(Graph.node.live(live, width, anchor, position)) == Chess.view.live(live, width, position) : Chess.View}:
  match live:
    case False{}:
      {==}
    case True{}:
      Equal.trans(Chess.View, Graph.view(Graph.node.live(live, width, anchor, position)),
        Chess.view.moves(position, Graph.positions(Graph.successors(width, anchor, position))), Chess.view.live(live, width, position),
        node_moves(position, Graph.successors(width, anchor, position)),
        Equal.cong(List<&2, P.Position>, Chess.View, children => Chess.view.moves(position, children),
          Graph.positions(Graph.successors(width, anchor, position)), Chess.successors(width, position), successors(width, anchor, position)))

def node(+width: Nat, +anchor: Game.Player, +position: P.Position) ->
  {Graph.view(Graph.node(width, anchor, position)) == Chess.view(width, position) : Chess.View}:
  match position:
    case P.Position{turn, wk, bk, men, ep, target}:
      node_live(Chess.valid(position) && Bool.not(Chess.insufficient(men)), width, anchor, position)
