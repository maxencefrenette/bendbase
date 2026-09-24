import Base
import ./chess_component.bend as Component
import ./position.bend as P
import ./game.bend as Game
import ./pawnless_chess.bend as Three
import ./chess.bend as Chess
import ./chess_measure.bend as Measure
import ./chess_selection_proof.bend as Selection
import ./position_address.bend as Address
import ./position_address_proof.bend as AddressProof
import ./chess_graph.bend as Graph
import ./chess_graph_proof.bend as GraphProof
import ./material_cache.bend as Registry
import ./position_index.bend as Index

def prepend(+anchor: Game.Player, +piece: P.Man, +packed: Address.Packed) ->
  {Component.packed_material(Address.prepend(anchor, piece, packed)) ==
    Component.man(anchor, piece) <> Component.packed_material(packed) : List<&2, P.Descriptor>}:
  match piece packed:
    case P.Man{owner, kind, square} Address.Packed{n, material, board}:
      {==}

def pack_men(+pieces: List<&2, P.Man>, +anchor: Game.Player, +frame: P.Frame) ->
  {Component.packed_material(Address.pack_men(pieces, anchor, frame)) == Component.men(anchor, pieces) : List<&2, P.Descriptor>}:
  match pieces:
    case Nil{}:
      {==}
    case +head <> +tail:
      Equal.trans(List<&2, P.Descriptor>, Component.packed_material(Address.pack_men(pieces, anchor, frame)),
        Component.man(anchor, head) <> Component.packed_material(Address.pack_men(tail, anchor, frame)), Component.men(anchor, pieces),
        prepend(anchor, head, Address.pack_men(tail, anchor, frame)),
        Equal.cong(List<&2, P.Descriptor>, List<&2, P.Descriptor>, rest => Component.man(anchor, head) <> rest,
          Component.packed_material(Address.pack_men(tail, anchor, frame)), Component.men(anchor, tail), pack_men(tail, anchor, frame)))

def encoded_material(+packed: Address.Packed) ->
  {Component.address_material(Address.encode(packed)) == Component.packed_material(packed) : List<&2, P.Descriptor>}:
  match packed:
    case Address.Packed{n, material, board}:
      {==}

def address_material(+anchor: Game.Player, +board: P.Position) ->
  {Component.address_material(Address.of_position(anchor, board)) == Component.material(anchor, board) : List<&2, P.Descriptor>}:
  match board:
    case P.Position{turn, wk, bk, pieces, ep, target}:
      Equal.trans(List<&2, P.Descriptor>, Component.address_material(Address.of_position(anchor, board)),
        Component.packed_material(Address.pack(anchor, board)), Component.material(anchor, board),
        encoded_material(Address.pack(anchor, board)), pack_men(pieces, anchor, P.Frame{anchor, turn, wk, bk, ep, target}))

def address_component(+anchor: Game.Player, +board: P.Position) ->
  {Component.of_address(Address.of_position(anchor, board)) == Component.of_position(anchor, board) : Component.Key}:
  %Equal.sym(P.Position, Address.position(Address.of_position(anchor, board)), board, AddressProof.roundtrip(anchor, board)) :
    {Component.Key{Measure.position(_), Component.address_material(Address.of_position(anchor, board))} == Component.of_position(anchor, board) : Component.Key}
  %address_material(anchor, board) :
    {Component.Key{Measure.position(board), Component.address_material(Address.of_position(anchor, board))} == Component.Key{Measure.position(board), _} : Component.Key}
  {==}

def quiet_man(+moving: Bool, +anchor: Game.Player, +owner: Game.Player, +kind: P.PieceKind,
  +at: Word(6n), +dest: Word(6n), +choice: Three.Material, no: Game.Truth(Bool.not(Measure.moving_pawn(moving, kind)))) ->
  {Component.man(anchor, Measure.moved(moving, owner, kind, at, dest, choice)) == Component.man(anchor, P.Man{owner, kind, at}) : P.Descriptor}:
  match moving kind:
    case False{} P.Pawn{}:
      {==}
    case True{} P.Pawn{}:
      match no:
    case False{} P.Piece{kind}:
      {==}
    case True{} P.Piece{kind}:
      {==}

def quiet_keep(+remove: Bool, +anchor: Game.Player, +next: P.Man, +old: P.Man, +tail: List<&2, P.Man>, +before: List<&2, P.Man>,
  no: Game.Truth(Bool.not(remove)), same: {Component.man(anchor, next) == Component.man(anchor, old) : P.Descriptor},
  rest: {Component.men(anchor, tail) == Component.men(anchor, before) : List<&2, P.Descriptor>}) ->
  {Component.men(anchor, Chess.keep(remove || False{}, next, tail)) == Component.men(anchor, old <> before) : List<&2, P.Descriptor>}:
  match remove:
    case True{}:
      match no:
    case False{}:
      %same : {Component.man(anchor, next) <> Component.men(anchor, tail) == _ <> Component.men(anchor, before) : List<&2, P.Descriptor>}
      %rest : {Component.man(anchor, next) <> Component.men(anchor, tail) == Component.man(anchor, next) <> _ : List<&2, P.Descriptor>}
      {==}

def quiet_update(+pieces: List<&2, P.Man>, +anchor: Game.Player, +from: Word(6n), +dest: Word(6n), +choice: Three.Material, +victim: Word(6n),
  +no_pawn: Game.Truth(Bool.not(Measure.pawns_moving(pieces, from))), +no_capture: Game.Truth(Bool.not(Chess.occupied(pieces, dest)))) ->
  {Component.men(anchor, Chess.move_men(pieces, from, dest, choice, False{}, victim)) == Component.men(anchor, pieces) : List<&2, P.Descriptor>}:
  match pieces:
    case Nil{}:
      {==}
    case P.Man{+owner, +kind, +at} <> +tail:
      quiet_keep(Chess.equal(at, dest), anchor, Measure.moved(Chess.equal(at, from), owner, kind, at, dest, choice), P.Man{owner, kind, at},
        Chess.move_men(tail, from, dest, choice, False{}, victim), tail,
        Selection.no_left(Chess.equal(at, dest), Chess.occupied(tail, dest), no_capture),
        quiet_man(Chess.equal(at, from), anchor, owner, kind, at, dest, choice,
          Selection.no_left(Measure.moving_pawn(Chess.equal(at, from), kind), Measure.pawns_moving(tail, from), no_pawn)),
        quiet_update(tail, anchor, from, dest, choice, victim,
          Selection.no_right(Measure.moving_pawn(Chess.equal(at, from), kind), Measure.pawns_moving(tail, from), no_pawn),
          Selection.no_right(Chess.equal(at, dest), Chess.occupied(tail, dest), no_capture)))

def legal_material(+anchor: Game.Player, +board: P.Position, +move: Chess.Action,
  legal: Game.Truth(Chess.legal(board, move)), +quiet: Game.Truth(Bool.not(Chess.resets(board, move)))) ->
  {Component.material(anchor, Chess.after(board, move)) == Component.material(anchor, board) : List<&2, P.Descriptor>}:
  match board move:
    case P.Position{+turn, wk, bk, +pieces, ep, target} Chess.Action{+from, +dest, +choice}:
      +no_pawn = Selection.no_left(Chess.pawn_move(board, move), Chess.occupied(pieces, dest), quiet)
      %Equal.sym(Bool, Chess.ep_move(board, move), False{}, Selection.no_ep(board, move, no_pawn)) :
        {Component.men(anchor, Chess.move_men(pieces, from, dest, choice, _, Chess.shift(Three.other(turn), dest))) == Component.men(anchor, pieces) : List<&2, P.Descriptor>}
      quiet_update(pieces, anchor, from, dest, choice, Chess.shift(Three.other(turn), dest),
        Selection.selection_quiet(pieces, board, turn, from, dest, Selection.legal_selection(board, move, legal), no_pawn),
        Selection.no_right(Chess.pawn_move(board, move), Chess.occupied(pieces, dest), quiet))

def legal_component(+anchor: Game.Player, +board: P.Position, +move: Chess.Action,
  +legal: Game.Truth(Chess.legal(board, move)), +quiet: Game.Truth(Bool.not(Chess.resets(board, move)))) ->
  {Component.of_position(anchor, Chess.after(board, move)) == Component.of_position(anchor, board) : Component.Key}:
  %Selection.legal_quiet(board, move, legal, quiet) :
    {Component.of_position(anchor, Chess.after(board, move)) == Component.Key{_, Component.material(anchor, board)} : Component.Key}
  %legal_material(anchor, board, move, legal, quiet) :
    {Component.of_position(anchor, Chess.after(board, move)) == Component.Key{Measure.position(Chess.after(board, move)), _} : Component.Key}
  {==}

def routed_component(+anchor: Game.Player, +board: P.Position, +move: Chess.Action,
  legal: Game.Truth(Chess.legal(board, move)), quiet: Game.Truth(Bool.not(Chess.resets(board, move)))) ->
  {Component.of_address(Graph.address(Graph.route(anchor, board, move))) == Component.of_position(anchor, board) : Component.Key}:
  %Equal.sym(Address.Address, Graph.address(Graph.route(anchor, board, move)), Address.of_position(anchor, Chess.after(board, move)),
    GraphProof.edge_address(Chess.resets(board, move), Address.of_position(anchor, Chess.after(board, move)))) :
    {Component.of_address(_) == Component.of_position(anchor, board) : Component.Key}
  Equal.trans(Component.Key, Component.of_address(Address.of_position(anchor, Chess.after(board, move))),
    Component.of_position(anchor, Chess.after(board, move)), Component.of_position(anchor, board),
    address_component(anchor, Chess.after(board, move)), legal_component(anchor, board, move, legal, quiet))

def signature_length(n: Nat, +material: P.Material(n)) ->
  {List.length(&2, P.Descriptor, Registry.signature(n, material)) == n : Nat}:
  match n material:
    case 0n Unit{}:
      {==}
    case 1n+rest P.MaterialCell{head, tail}:
      %signature_length(rest, tail) : {1n+List.length(&2, P.Descriptor, Registry.signature(rest, tail)) == 1n+_ : Nat}
      {==}

def width_agrees(+address: Address.Address) ->
  {Component.address_width(address) == Component.width(Component.of_address(address)) : Nat}:
  match address:
    case Address.Address{n, material, key}:
      Equal.cong(Nat, Nat, count => Index.width(count), n, List.length(&2, P.Descriptor, Registry.signature(n, material)),
        Equal.sym(Nat, List.length(&2, P.Descriptor, Registry.signature(n, material)), n, signature_length(n, material)))

def routed_width(+anchor: Game.Player, +board: P.Position, +move: Chess.Action,
  legal: Game.Truth(Chess.legal(board, move)), quiet: Game.Truth(Bool.not(Chess.resets(board, move)))) ->
  {Component.address_width(Graph.address(Graph.route(anchor, board, move))) == Component.address_width(Address.of_position(anchor, board)) : Nat}:
  %Equal.sym(Nat, Component.address_width(Graph.address(Graph.route(anchor, board, move))),
    Component.width(Component.of_address(Graph.address(Graph.route(anchor, board, move)))), width_agrees(Graph.address(Graph.route(anchor, board, move)))) :
    {_ == Component.address_width(Address.of_position(anchor, board)) : Nat}
  %Equal.sym(Component.Key, Component.of_address(Graph.address(Graph.route(anchor, board, move))), Component.of_position(anchor, board),
    routed_component(anchor, board, move, legal, quiet)) : {Component.width(_) == Component.address_width(Address.of_position(anchor, board)) : Nat}
  %address_component(anchor, board) : {Component.width(_) == Component.address_width(Address.of_position(anchor, board)) : Nat}
  Equal.sym(Nat, Component.address_width(Address.of_position(anchor, board)), Component.width(Component.of_address(Address.of_position(anchor, board))),
    width_agrees(Address.of_position(anchor, board)))
