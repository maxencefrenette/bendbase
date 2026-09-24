import Base
import ./position.bend as Position
import ./pawnless_chess.bend as Three
import ./pawnless_index.bend as ThreeIndex
import ./word_parts.bend as Parts

# One layout for every material: six square bits per non-king slot, followed
# by ep-enabled, owner, turn, ep-target, black king, white king (21 bits).
# Used by the direct common writer; specialized .wdl files retain their indexes.
def width(n: Nat) -> Nat:
  match n:
    case 0n:
      21n
    case 1n+rest:
      Nat.add(6n, width(rest))

def frame_encode(frame: Position.Frame) -> Word(21n):
  match frame:
    case Position.Frame{owner, turn, wk, bk, ep, ep_square}:
      WCon{ep, ThreeIndex.encode(Three.Board{owner, turn, wk, bk, ep_square})}

def frame_parts(ep: Bool, board: Three.Board) -> Position.Frame:
  match board:
    case Three.Board{owner, turn, wk, bk, ep_square}:
      Position.Frame{owner, turn, wk, bk, ep, ep_square}

def frame_decode(key: Word(21n)) -> Position.Frame:
  match key:
    case WCon{ep, tail}:
      frame_parts(ep, ThreeIndex.decode(tail))

def encode(n: Nat, board: Position.Board(n)) -> Word(width(n)):
  match n board:
    case 0n frame:
      frame_encode(frame)
    case 1n++rest Position.Slot{square, tail}:
      Parts.append(width(rest), 6n, square, encode(rest, tail))

def square(-n: Nat, pair: Word(6n) & Word(width(n))) -> Word(6n):
  match pair:
    case Tuple{square, tail}:
      square

def tail(-n: Nat, pair: Word(6n) & Word(width(n))) -> Word(width(n)):
  match pair:
    case Tuple{square, tail}:
      tail

def decode(n: Nat, +key: Word(width(n))) -> Position.Board(n):
  match n:
    case 0n:
      frame_decode(key)
    case 1n++rest:
      Position.Slot{square(rest, Parts.split(width(rest), 6n, key)),
        decode(rest, tail(rest, Parts.split(width(rest), 6n, key)))}
