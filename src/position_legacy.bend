import Base
import ./position.bend as Position
import ./pawnless_chess.bend as Three
import ./pawn_chess.bend as Pawn
import ./four_index.bend as Four
import ./material_chess.bend as Material
import ./pawnless_index.bend as Index

def no_target() -> Word(6n):
  Index.fit(6n, 0n, WNil{})

# Compatibility at the boundary only. The new representation has one shape
# parameter (piece count), not one board type per material family.
def three_material(kind: Position.PieceKind) -> Position.Material(1n):
  Position.MaterialCell{Position.Descriptor{False{}, kind}, Unit{}}

def four_material(material: Four.Material) -> Position.Material(2n):
  match material:
    case Four.Material{first, second, opposed}:
      Position.MaterialCell{Position.Descriptor{False{}, Position.Piece{first}},
        Position.MaterialCell{Position.Descriptor{opposed, Position.Piece{second}}, Unit{}}}

def from_three(board: Three.Board) -> Position.Board(1n):
  match board:
    case Three.Board{owner, turn, wk, bk, pc}:
      Position.Slot{pc, Position.Frame{owner, turn, wk, bk, False{}, no_target()}}

def to_three(board: Position.Board(1n)) -> Three.Board:
  match board:
    case Position.Slot{pc, Position.Frame{owner, turn, wk, bk, ep, ep_square}}:
      Three.Board{owner, turn, wk, bk, pc}

def from_four(board: Four.Board) -> Position.Board(2n):
  match board:
    case Four.Board{Three.Board{owner, turn, wk, bk, pc}, second}:
      Position.Slot{pc, Position.Slot{second, Position.Frame{owner, turn, wk, bk, False{}, no_target()}}}

def to_four(board: Position.Board(2n)) -> Four.Board:
  match board:
    case Position.Slot{pc, Position.Slot{second, Position.Frame{owner, turn, wk, bk, ep, ep_square}}}:
      Four.Board{Three.Board{owner, turn, wk, bk, pc}, second}

def lift_men(men: List<&2, Material.Man>) -> List<&2, Position.Man>:
  match men:
    case Nil{}:
      Nil{}
    case Material.Man{owner, kind, square} <> tail:
      Position.Man{owner, Position.Piece{kind}, square} <> lift_men(tail)

def lift_pawnless(position: Material.Position) -> Position.Position:
  match position:
    case Material.Position{turn, wk, bk, men}:
      Position.Position{turn, wk, bk, lift_men(men), False{}, no_target()}

def from_kpk(advance: Nat, position: Pawn.Position) -> Position.Board(1n):
  from_three(Pawn.board(advance, position))

def lift_kpk(advance: Nat, position: Pawn.Position) -> Position.Position:
  match position:
    case Pawn.Position{+owner, turn, wk, bk, file}:
      Position.Position{turn, wk, bk,
        Position.Man{owner, Position.Pawn{}, Pawn.square(Pawn.rank(advance, owner), file)} <> Nil{},
        False{}, no_target()}
