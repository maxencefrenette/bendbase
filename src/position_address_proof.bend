import Base
import ./game.bend as Game
import ./position.bend as P
import ./position_address.bend as Address
import ./position_index.bend as Index
import ./position_index_proof.bend as IndexProof
import ./pawnless_chess.bend as Three

def relative_owner(+anchor: Game.Player, +owner: Game.Player) ->
  {P.owner(anchor, Bool.not(Three.same(anchor, owner))) == owner : Game.Player}:
  match anchor owner:
    case Game.White{} Game.White{}:
      {==}
    case Game.White{} Game.Black{}:
      {==}
    case Game.Black{} Game.White{}:
      {==}
    case Game.Black{} Game.Black{}:
      {==}

def prepend_frame(+anchor: Game.Player, +man: P.Man, +packed: Address.Packed) ->
  {Address.frame(Address.prepend(anchor, man, packed)) == Address.frame(packed) : P.Frame}:
  match man packed:
    case P.Man{owner, kind, square} Address.Packed{n, material, board}:
      {==}

def pack_frame(men: List<&2, P.Man>, +anchor: Game.Player, +frame: P.Frame) ->
  {Address.frame(Address.pack_men(men, anchor, frame)) == frame : P.Frame}:
  match men:
    case Nil{}:
      {==}
    case +head <> +tail:
      Equal.trans(P.Frame, Address.frame(Address.pack_men(head <> tail, anchor, frame)),
        Address.frame(Address.pack_men(tail, anchor, frame)), frame,
        prepend_frame(anchor, head, Address.pack_men(tail, anchor, frame)), pack_frame(tail, anchor, frame))

def prepend_men(+anchor: Game.Player, +man: P.Man, +packed: Address.Packed) ->
  {Address.men(Address.prepend(anchor, man, packed), anchor) == man <> Address.men(packed, anchor) : List<&2, P.Man>}:
  match man packed:
    case P.Man{owner, kind, square} Address.Packed{n, material, board}:
      Equal.cong(Game.Player, List<&2, P.Man>, player => P.Man{player, kind, square} <> P.men(n, material, board, anchor),
        P.owner(anchor, Bool.not(Three.same(anchor, owner))), owner, relative_owner(anchor, owner))

def pack_men(+men: List<&2, P.Man>, +anchor: Game.Player, +frame: P.Frame) ->
  {Address.men(Address.pack_men(men, anchor, frame), anchor) == men : List<&2, P.Man>}:
  match men:
    case Nil{}:
      {==}
    case head <> tail:
      Equal.trans(List<&2, P.Man>, Address.men(Address.pack_men(men, anchor, frame), anchor),
        head <> Address.men(Address.pack_men(tail, anchor, frame), anchor), men,
        prepend_men(anchor, head, Address.pack_men(tail, anchor, frame)),
        Equal.cong(List<&2, P.Man>, List<&2, P.Man>, rest => head <> rest,
          Address.men(Address.pack_men(tail, anchor, frame), anchor), tail, pack_men(tail, anchor, frame)))

def unpack_frame(+packed: Address.Packed, +frame: P.Frame, equal: {Address.frame(packed) == frame : P.Frame}) ->
  {Address.unpack(packed) == P.assemble(frame, Address.men(packed, P.anchor(frame))) : P.Position}:
  Equal.cong(P.Frame, P.Position, base => P.assemble(base, Address.men(packed, P.anchor(base))),
    Address.frame(packed), frame, equal)

def pack_roundtrip(+anchor: Game.Player, +position: P.Position) ->
  {Address.unpack(Address.pack(anchor, position)) == position : P.Position}:
  match position:
    case P.Position{turn, wk, bk, men, ep, target}:
      +frame = {P.Frame{anchor, turn, wk, bk, ep, target} : P.Frame}
      +packed = Address.pack_men(men, anchor, frame)
      Equal.trans(P.Position, Address.unpack(packed), P.assemble(frame, Address.men(packed, anchor)), position,
        unpack_frame(packed, frame, pack_frame(men, anchor, frame)),
        Equal.cong(List<&2, P.Man>, P.Position, pieces => P.assemble(frame, pieces),
          Address.men(packed, anchor), men, pack_men(men, anchor, frame)))

def index_roundtrip(+packed: Address.Packed) ->
  {Address.decode(Address.encode(packed)) == packed : Address.Packed}:
  match packed:
    case Address.Packed{n, material, board}:
      Equal.cong(P.Board(n), Address.Packed, b => Address.Packed{n, material, b},
        Index.decode(n, Index.encode(n, board)), board, IndexProof.roundtrip(n, board))

def roundtrip(+anchor: Game.Player, +position: P.Position) ->
  {Address.position(Address.of_position(anchor, position)) == position : P.Position}:
  Equal.trans(P.Position, Address.position(Address.of_position(anchor, position)), Address.unpack(Address.pack(anchor, position)), position,
    Equal.cong(Address.Packed, P.Position, packed => Address.unpack(packed),
      Address.decode(Address.encode(Address.pack(anchor, position))), Address.pack(anchor, position), index_roundtrip(Address.pack(anchor, position))),
    pack_roundtrip(anchor, position))

def injective(+left_anchor: Game.Player, +right_anchor: Game.Player, +left: P.Position, +right: P.Position,
  same: {Address.of_position(left_anchor, left) == Address.of_position(right_anchor, right) : Address.Address}) ->
  {left == right : P.Position}:
  %roundtrip(left_anchor, left) : {_ == right : P.Position}
  %roundtrip(right_anchor, right) : {Address.position(Address.of_position(left_anchor, left)) == _ : P.Position}
  Equal.cong(Address.Address, P.Position, address => Address.position(address),
    Address.of_position(left_anchor, left), Address.of_position(right_anchor, right), same)
