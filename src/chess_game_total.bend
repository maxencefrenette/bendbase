import Base
import ./chess_game.bend as S
import ./chess.bend as Chess
import ./chess_graph.bend as Graph
import ./chess_graph_proof.bend as GraphProof
import ./chess_measure.bend as M
import ./chess_measure_proof.bend as MeasureProof
import ./chess_compile_total.bend as Total
import ./material_directory_proof.bend as DirectoryProof
import ./position.bend as P
import ./position_address.bend as Address
import ./finite_table.bend as Finite
import ./game.bend as Game

def Edges(edges: List<&2, Graph.Edge>, +limit: Nat, +remaining: Nat, +fuel: Nat) -> Type:
  match edges:
    case Nil{}:
      Unit
    case +head <> tail:
      M.Le(M.budget(limit, M.position(Address.position(Graph.address(head))), Graph.next_clock(limit, remaining, head)), fuel) & Edges(tail, limit, remaining, fuel)

def States(items: List<&2, S.State>, +limit: Nat, +fuel: Nat) -> Type:
  match items:
    case Nil{}:
      Unit
    case S.State{remaining, position} <> tail:
      M.Le(M.budget(limit, M.position(position), remaining), fuel) & States(tail, limit, fuel)

def states(+edges: List<&2, Graph.Edge>, +limit: Nat, +remaining: Nat, +fuel: Nat, bounded: Edges(edges, limit, remaining, fuel)) ->
  States(S.states(limit, remaining, edges), limit, fuel):
  match edges:
    case Nil{}:
      Unit{}
    case head <> tail:
      (first, rest) = bounded
      (first, states(tail, limit, remaining, fuel, rest))

def include(+allowed: Bool, +limit: Nat, +clock: Nat, +fuel: Nat, +board: P.Position, +move: Chess.Action, +tail: List<&2, Graph.Edge>,
  legal: {Chess.legal(board, move) == allowed : Bool}, bounded: M.Le(M.budget(limit, M.position(board), 1n+clock), 1n+fuel), rest: Edges(tail, limit, 1n+clock, fuel)) ->
  Edges(Graph.include(allowed, Graph.route(Game.White{}, board, move), tail), limit, 1n+clock, fuel):
  match allowed:
    case False{}:
      rest
    case True{}:
      (MeasureProof.trans(1n+M.budget(limit, M.position(Address.position(Graph.address(Graph.route(Game.White{}, board, move)))),
        Graph.next_clock(limit, 1n+clock, Graph.route(Game.White{}, board, move))), M.budget(limit, M.position(board), 1n+clock), 1n+fuel,
        GraphProof.route_budget(limit, clock, Game.White{}, board, move, DirectoryProof.matches_true(Chess.legal(board, move), legal)), bounded), rest)

def scan(depth: Nat, +width: Nat, +limit: Nat, +clock: Nat, +fuel: Nat, +board: P.Position,
  +keys: Finite.Table(depth, Word(width)), +tail: List<&2, Graph.Edge>, bounded: M.Le(M.budget(limit, M.position(board), 1n+clock), 1n+fuel),
  rest: Edges(tail, limit, 1n+clock, fuel)) -> Edges(Graph.scan(depth, width, Game.White{}, board, keys, tail), limit, 1n+clock, fuel):
  match depth keys:
    case 0n key:
      include(Chess.legal(board, Chess.action_at(width, key)), limit, clock, fuel, board, Chess.action_at(width, key), tail, {==}, bounded, rest)
    case 1n++prior Finite.Fork{left, right}:
      Total.compose(M.Le(M.budget(limit, M.position(board), 1n+clock), 1n+fuel), Unit,
        Edges(tail, limit, 1n+clock, fuel), Edges(Graph.scan(prior, width, Game.White{}, board, right, tail), limit, 1n+clock, fuel),
        Edges(Graph.scan(prior, width, Game.White{}, board, left, Graph.scan(prior, width, Game.White{}, board, right, tail)), limit, 1n+clock, fuel),
        Total.bounds(M.budget(limit, M.position(board), 1n+clock), 1n+fuel, bounded), (Unit{}, Unit{}), rest,
        bound => unit => more => scan(prior, width, limit, clock, fuel, board, right, tail, bound, more),
        bound => unit => more => scan(prior, width, limit, clock, fuel, board, left, Graph.scan(prior, width, Game.White{}, board, right, tail), bound, more))

def moves(+board: P.Position, +edges: List<&2, Graph.Edge>, +limit: Nat, +clock: Nat, +fuel: Nat,
  bounded: Edges(edges, limit, 1n+clock, fuel)) -> Edges(S.children(Graph.node.moves(board, edges)), limit, 1n+clock, fuel):
  match board edges:
    case P.Position{turn, wk, bk, men, ep, square} Nil{}:
      Unit{}
    case P.Position{turn, wk, bk, men, ep, square} head <> tail:
      bounded

def live(+allowed: Bool, +actions: Nat, +board: P.Position, +limit: Nat, +clock: Nat, +fuel: Nat,
  bounded: M.Le(M.budget(limit, M.position(board), 1n+clock), 1n+fuel)) ->
  Edges(S.children(Graph.node.live(allowed, actions, Game.White{}, board)), limit, 1n+clock, fuel):
  match allowed:
    case False{}:
      Unit{}
    case True{}:
      moves(board, Graph.successors(actions, Game.White{}, board), limit, clock, fuel,
        scan(actions, actions, limit, clock, fuel, board, Finite.keys(actions), Nil{}, bounded, Unit{}))

def node(+actions: Nat, +board: P.Position, +limit: Nat, +clock: Nat, +fuel: Nat,
  bounded: M.Le(M.budget(limit, M.position(board), 1n+clock), 1n+fuel)) ->
  Edges(S.children(Graph.node(actions, Game.White{}, board)), limit, 1n+clock, fuel):
  match board:
    case P.Position{turn, wk, bk, men, ep, square}:
      live(Chess.valid(board) && Bool.not(Chess.insufficient(men)), actions, board, limit, clock, fuel, bounded)

def positive(+board: P.Position, limit: Nat, remaining: Nat, impossible: M.Le(M.budget(limit, M.position(board), remaining), 0n)) -> Empty:
  match board:
    case P.Position{turn, wk, bk, men, ep, square}:
      match impossible:

def forest(+fuel: Nat, +items: List<&2, S.State>, +limit: Nat, +actions: Nat, bounded: States(items, limit, fuel)) -> S.NoCutoff(fuel, items, limit, actions):
  match fuel items:
    case 0n Nil{}:
      Unit{}
    case 1n+prior Nil{}:
      Unit{}
    case 0n S.State{remaining, board} <> tail:
      (first, rest) = bounded
      positive(board, limit, remaining, first)
    case 1n++prior S.State{0n, board} <> tail:
      (first, rest) = bounded
      forest(1n+prior, tail, limit, actions, rest)
    case 1n++prior S.State{1n+clock, board} <> tail:
      (first, rest) = bounded
      (forest(prior, S.states(limit, 1n+clock, S.children(Graph.node(actions, Game.White{}, board))), limit, actions,
        states(S.children(Graph.node(actions, Game.White{}, board)), limit, 1n+clock, prior, node(actions, board, limit, clock, prior, first))),
        forest(1n+prior, tail, limit, actions, rest))

def complete(+limit: Nat, +remaining: Nat, +actions: Nat, +board: P.Position) ->
  S.NoCutoff(M.budget(limit, M.position(board), remaining), [S.State{remaining, board}], limit, actions):
  forest(M.budget(limit, M.position(board), remaining), [S.State{remaining, board}], limit, actions,
    (MeasureProof.refl(M.budget(limit, M.position(board), remaining)), Unit{}))
