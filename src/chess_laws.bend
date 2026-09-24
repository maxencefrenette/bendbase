import Base
import ./game.bend as Game
import ./pawnless_chess.bend as Chess
import ./position.bend as Position
import ./position_index.bend as PositionIndex
import ./chess.bend as CommonChess
import ./position_address.bend as PositionAddress
import ./chess_graph.bend as ChessGraph
import ./chess_measure.bend as Measure
import ./chess_component.bend as ChessComponent

# Supporting laws for common chess: representation, lossless addresses,
# quiet-component closure, pawn progress, and the decreasing continuation bound.
# The measure is two kings + one per other man + summed pawn promotion distance;
# (limit + 1) * measure + remaining decreases on every legal continuation.
# These lemmas support the public no-cutoff and WDL contracts in ../LAWS.bend.
# They also support the cached alternative without establishing its semantics.
# Every law here is discharged by ../PROOF.bend.

law common_address_preserves_component:
  for +anchor: Game.Player
  for +board: Position.Position
  {ChessComponent.of_address(PositionAddress.of_position(anchor, board)) == ChessComponent.of_position(anchor, board) : ChessComponent.Key}

law common_legal_quiet_moves_preserve_material:
  for +anchor: Game.Player
  for +board: Position.Position
  for +move: CommonChess.Action
  for legal: Game.Truth(CommonChess.legal(board, move))
  for quiet: Game.Truth(Bool.not(CommonChess.resets(board, move)))
  {ChessComponent.material(anchor, CommonChess.after(board, move)) == ChessComponent.material(anchor, board) : List<&2, Position.Descriptor>}

law common_quiet_routes_stay_in_component:
  for +anchor: Game.Player
  for +board: Position.Position
  for +move: CommonChess.Action
  for legal: Game.Truth(CommonChess.legal(board, move))
  for quiet: Game.Truth(Bool.not(CommonChess.resets(board, move)))
  {ChessComponent.of_address(ChessGraph.address(ChessGraph.route(anchor, board, move))) == ChessComponent.of_position(anchor, board) : ChessComponent.Key}

law common_quiet_routes_preserve_key_width:
  for +anchor: Game.Player
  for +board: Position.Position
  for +move: CommonChess.Action
  for legal: Game.Truth(CommonChess.legal(board, move))
  for quiet: Game.Truth(Bool.not(CommonChess.resets(board, move)))
  {ChessComponent.address_width(ChessGraph.address(ChessGraph.route(anchor, board, move))) ==
    ChessComponent.address_width(PositionAddress.of_position(anchor, board)) : Nat}

law common_pawn_geometry_decreases_distance:
  for +owner: Game.Player
  for +from: Word(6n)
  for +dest: Word(6n)
  for +board: Position.Position
  for allowed: Game.Truth(CommonChess.pawn_geometry(owner, from, dest, board))
  Measure.Lt(Measure.distance(owner, dest), Measure.distance(owner, from))

law common_move_update_respects_measure:
  for +pieces: List<&2, Position.Man>
  for +from: Word(6n)
  for +dest: Word(6n)
  for +choice: Chess.Material
  for +ep: Bool
  for +victim: Word(6n)
  for progress: Measure.Progress(pieces, from, dest)
  Measure.Bound(Measure.changes(pieces, from, dest, ep, victim),
    Measure.men(CommonChess.move_men(pieces, from, dest, choice, ep, victim)), Measure.men(pieces))

law common_legal_resets_decrease_measure:
  for +board: Position.Position
  for +move: CommonChess.Action
  for legal: Game.Truth(CommonChess.legal(board, move))
  for reset: Game.Truth(CommonChess.resets(board, move))
  Measure.Lt(Measure.position(CommonChess.after(board, move)), Measure.position(board))

law common_legal_quiet_moves_preserve_measure:
  for +board: Position.Position
  for +move: CommonChess.Action
  for legal: Game.Truth(CommonChess.legal(board, move))
  for quiet: Game.Truth(Bool.not(CommonChess.resets(board, move)))
  {Measure.position(CommonChess.after(board, move)) == Measure.position(board) : Nat}

law common_legal_continuations_decrease_budget:
  for +limit: Nat
  for +remaining: Nat
  for +board: Position.Position
  for +move: CommonChess.Action
  for legal: Game.Truth(CommonChess.legal(board, move))
  Measure.Lt(Measure.budget(limit, Measure.position(CommonChess.after(board, move)),
    Bool.pick(Nat, CommonChess.resets(board, move), limit, remaining)),
    Measure.budget(limit, Measure.position(board), 1n+remaining))

law common_routed_continuations_decrease_budget:
  for +limit: Nat
  for +remaining: Nat
  for +anchor: Game.Player
  for +board: Position.Position
  for +move: CommonChess.Action
  for legal: Game.Truth(CommonChess.legal(board, move))
  Measure.Lt(Measure.budget(limit, Measure.position(PositionAddress.position(ChessGraph.address(ChessGraph.route(anchor, board, move)))),
    ChessGraph.next_clock(limit, 1n+remaining, ChessGraph.route(anchor, board, move))),
    Measure.budget(limit, Measure.position(board), 1n+remaining))

law successor_addresses_are_lossless:
  for +anchor: Game.Player
  for +position: Position.Position
  {PositionAddress.position(PositionAddress.of_position(anchor, position)) == position : Position.Position}

law successor_addresses_cannot_alias_distinct_positions:
  for +left_anchor: Game.Player
  for +right_anchor: Game.Player
  for +left: Position.Position
  for +right: Position.Position
  for same: {PositionAddress.of_position(left_anchor, left) == PositionAddress.of_position(right_anchor, right) : PositionAddress.Address}
  {left == right : Position.Position}

law common_graph_routes_to_actual_successor:
  for +anchor: Game.Player
  for +position: Position.Position
  for +move: CommonChess.Action
  {PositionAddress.position(ChessGraph.address(ChessGraph.route(anchor, position, move))) ==
   CommonChess.after(position, move) : Position.Position}

law common_graph_preserves_clock_reset:
  for +anchor: Game.Player
  for +position: Position.Position
  for +move: CommonChess.Action
  {ChessGraph.resets(ChessGraph.route(anchor, position, move)) == CommonChess.resets(position, move) : Bool}

law common_graph_applies_clock_policy:
  for +limit: Nat
  for +remaining: Nat
  for +anchor: Game.Player
  for +position: Position.Position
  for +move: CommonChess.Action
  {ChessGraph.next_clock(limit, remaining, ChessGraph.route(anchor, position, move)) ==
   Bool.pick(Nat, CommonChess.resets(position, move), limit, Nat.sub(remaining, 1n)) : Nat}

law common_graph_preserves_all_moves_and_terminal_results:
  for +width: Nat
  for +anchor: Game.Player
  for +position: Position.Position
  {ChessGraph.view(ChessGraph.node(width, anchor, position)) == CommonChess.view(width, position) : CommonChess.View}

law general_position_index_roundtrip:
  for +n: Nat
  for +board: Position.Board(n)
  {PositionIndex.decode(n, PositionIndex.encode(n, board)) == board : Position.Board(n)}

law general_position_index_is_injective:
  for +n: Nat
  for +left: Position.Board(n)
  for +right: Position.Board(n)
  for same: {PositionIndex.encode(n, left) == PositionIndex.encode(n, right) : Word(PositionIndex.width(n))}
  {left == right : Position.Board(n)}

law general_material_has_exact_piece_count:
  for +n: Nat
  for +material: Position.Material(n)
  for +board: Position.Board(n)
  for +owner: Game.Player
  {List.length(&2, Position.Man, Position.men(n, material, board, owner)) == n : Nat}
