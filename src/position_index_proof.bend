import Base
import ./game.bend as Game
import ./position.bend as Position
import ./position_index.bend as Index
import ./pawnless_chess.bend as Three
import ./pawnless_index.bend as ThreeIndex
import ./pawnless_index_proof.bend as ThreeProof
import ./word_parts.bend as Parts

def frame_roundtrip(+frame: Position.Frame) ->
  {Index.frame_decode(Index.frame_encode(frame)) == frame : Position.Frame}:
  match frame:
    case Position.Frame{owner, turn, wk, bk, +ep, ep_square}:
      +base = {Three.Board{owner, turn, wk, bk, ep_square} : Three.Board}
      Equal.cong(Three.Board, Position.Frame, board => Index.frame_parts(ep, board),
        ThreeIndex.decode(ThreeIndex.encode(base)), base, ThreeProof.decode_encode(base))

def roundtrip(n: Nat, +board: Position.Board(n)) ->
  {Index.decode(n, Index.encode(n, board)) == board : Position.Board(n)}:
  match n board:
    case 0n frame:
      frame_roundtrip(frame)
    case 1n++rest Position.Slot{+square, +tail}:
      %roundtrip(rest, tail) :
        {Index.decode(1n+rest, Index.encode(1n+rest, board)) == Position.Slot{square, _} : Position.Board(1n+rest)}
      %Equal.sym(Word(6n) & Word(Index.width(rest)),
        Parts.split(Index.width(rest), 6n, Parts.append(Index.width(rest), 6n, square, Index.encode(rest, tail))),
        (square, Index.encode(rest, tail)),
        ThreeProof.split_append(6n, Index.width(rest), square, Index.encode(rest, tail))) :
        {Position.Slot{Index.square(rest, _), Index.decode(rest, Index.tail(rest, _))} ==
         Position.Slot{square, Index.decode(rest, Index.encode(rest, tail))} : Position.Board(1n+rest)}
      {==}

def injective(+n: Nat, +left: Position.Board(n), +right: Position.Board(n),
  same: {Index.encode(n, left) == Index.encode(n, right) : Word(Index.width(n))}) ->
  {left == right : Position.Board(n)}:
  %roundtrip(n, left) : {_ == right : Position.Board(n)}
  %roundtrip(n, right) : {Index.decode(n, Index.encode(n, left)) == _ : Position.Board(n)}
  Equal.cong(Word(Index.width(n)), Position.Board(n), key => Index.decode(n, key),
    Index.encode(n, left), Index.encode(n, right), same)

def men_count(n: Nat, +material: Position.Material(n), +board: Position.Board(n), +owner: Game.Player) ->
  {List.length(&2, Position.Man, Position.men(n, material, board, owner)) == n : Nat}:
  match n material board:
    case 0n Unit{} frame:
      {==}
    case 1n+rest Position.MaterialCell{Position.Descriptor{opposed, kind}, tail} Position.Slot{square, more}:
      %men_count(rest, tail, more, owner) :
        {1n+List.length(&2, Position.Man, Position.men(rest, tail, more, owner)) == 1n+_ : Nat}
      {==}
