import Base
import ./game.bend as Game
import ./pawnless_chess.bend as Three

# A material signature fixes kinds and ownership relative to Frame.owner.
# Slot order is stable, including for identical pieces; no symmetry reduction.
# Kings are separate, so n below always counts NON-KING pieces.
type PieceKind is Data:
  Pawn{}
  Piece{kind: Three.Material}

type Descriptor is Data:
  Descriptor{opposed: Bool, kind: PieceKind}

law Material:
  for n: Nat
  Data

type MaterialCell<-n: Nat> is Data:
  MaterialCell{head: Descriptor, tail: Material(n)}

def Material(n):
  match n:
    case 0n:
      Unit
    case 1n+rest:
      MaterialCell<rest>

# EP is explicit continuation state. When ep is False, ep_square is ignored
# by chess rules but retained by the index: decoding never loses information.
# Stored roots will fix ep=False; castling and repetition history are excluded.
type Frame is Data:
  Frame{owner: Game.Player, turn: Game.Player, wk: Word(6n), bk: Word(6n),
    ep: Bool, ep_square: Word(6n)}

law Board:
  for n: Nat
  Data

type Slot<-n: Nat> is Data:
  Slot{square: Word(6n), tail: Board(n)}

def Board(n):
  match n:
    case 0n:
      Frame
    case 1n+rest:
      Slot<rest>

type Man is Data:
  Man{owner: Game.Player, kind: PieceKind, square: Word(6n)}

type Position is Data:
  Position{turn: Game.Player, wk: Word(6n), bk: Word(6n), men: List<&2, Man>,
    ep: Bool, ep_square: Word(6n)}

def frame(n: Nat, board: Board(n)) -> Frame:
  match n board:
    case 0n frame:
      frame
    case 1n+rest Slot{square, tail}:
      frame(rest, tail)

def anchor(frame: Frame) -> Game.Player:
  match frame:
    case Frame{owner, turn, wk, bk, ep, ep_square}:
      owner

def owner(+anchor: Game.Player, opposed: Bool) -> Game.Player:
  Bool.pick(Game.Player, opposed, Three.other(anchor), anchor)

def men(n: Nat, material: Material(n), board: Board(n), +anchor: Game.Player) -> List<&2, Man>:
  match n material board:
    case 0n Unit{} frame:
      Nil{}
    case 1n+rest MaterialCell{Descriptor{opposed, kind}, tail} Slot{square, more}:
      Man{owner(anchor, opposed), kind, square} <> men(rest, tail, more, anchor)

def assemble(frame: Frame, men: List<&2, Man>) -> Position:
  match frame:
    case Frame{owner, turn, wk, bk, ep, ep_square}:
      Position{turn, wk, bk, men, ep, ep_square}

def position(+n: Nat, material: Material(n), +board: Board(n)) -> Position:
  +base = frame(n, board)
  assemble(base, men(n, material, board, anchor(base)))
