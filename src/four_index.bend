import Base
import ./game.bend as Game
import ./pawnless_chess.bend as Three
import ./pawnless_index.bend as Index
import ./material_chess.bend as Chess
import ./word_parts.bend as Parts

# One file per pair of kinds and ownership relation. The owner's color is
# encoded in each slot, so both color reversals live in the same file.
type Material is Data:
  Material{first: Three.Material, second: Three.Material, opposed: Bool}

type Board is Data:
  Board{base: Three.Board, second: Word(6n)}

def position(material: Material, board: Board) -> Chess.Position:
  match material board:
    case Material{first, second, opposed} Board{Three.Board{+owner, turn, wk, bk, pc}, other}:
      Chess.Position{turn, wk, bk,
        Chess.Man{owner, first, pc} <> Chess.Man{Bool.pick(Game.Player, opposed, Three.other(owner), owner), second, other} <> Nil{}}

# MSB first: second square[5..0], then the existing 20-bit three-man index.
def encode(board: Board) -> Word(26n):
  match board:
    case Board{base, second}:
      Parts.append(20n, 6n, second, Index.encode(base))

def decode.parts(pair: Word(6n) & Word(20n)) -> Board:
  match pair:
    case Tuple{second, base}:
      Board{Index.decode(base), second}

def decode(key: Word(26n)) -> Board:
  decode.parts(Parts.split(20n, 6n, key))

def encode_at(width: Nat, board: Board) -> Word(width):
  Index.fit(width, 26n, encode(board))

def decode_at(+width: Nat, key: Word(width)) -> Board:
  decode(Index.fit(26n, width, key))
