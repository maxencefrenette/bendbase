import Base
import ./position.bend as Position
import ./position_legacy.bend as Legacy
import ./pawnless_chess.bend as Three
import ./pawn_chess.bend as Pawn
import ./four_index.bend as Four
import ./material_chess.bend as Material

def three_roundtrip(+board: Three.Board) ->
  {Legacy.to_three(Legacy.from_three(board)) == board : Three.Board}:
  match board:
    case Three.Board{owner, turn, wk, bk, pc}:
      {==}

def four_roundtrip(+board: Four.Board) ->
  {Legacy.to_four(Legacy.from_four(board)) == board : Four.Board}:
  match board:
    case Four.Board{Three.Board{owner, turn, wk, bk, pc}, second}:
      {==}

def three_position(+kind: Three.Material, +board: Three.Board) ->
  {Position.position(1n, Legacy.three_material(Position.Piece{kind}), Legacy.from_three(board)) ==
   Legacy.lift_pawnless(Material.from_three(kind, board)) : Position.Position}:
  match board:
    case Three.Board{owner, turn, wk, bk, pc}:
      {==}

def four_position(+material: Four.Material, +board: Four.Board) ->
  {Position.position(2n, Legacy.four_material(material), Legacy.from_four(board)) ==
   Legacy.lift_pawnless(Four.position(material, board)) : Position.Position}:
  match material board:
    case Four.Material{first, second, opposed} Four.Board{Three.Board{owner, turn, wk, bk, pc}, other}:
      {==}

def kpk_position(+advance: Nat, +position: Pawn.Position) ->
  {Position.position(1n, Legacy.three_material(Position.Pawn{}), Legacy.from_kpk(advance, position)) ==
   Legacy.lift_kpk(advance, position) : Position.Position}:
  match position:
    case Pawn.Position{owner, turn, wk, bk, file}:
      {==}
