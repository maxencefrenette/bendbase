import Base
import ./game.bend as Game
import ./position.bend as P
import ./position_index.bend as Index
import ./pawnless_chess.bend as Three

# Runtime-sized material and board travel together. A capture changes n;
# promotion changes the signature; a pawn push changes only the board.
# No three-/four-man or pawn-family dispatch is needed to construct an address.
type Packed is Data:
  Packed{n: Nat, material: P.Material(n), board: P.Board(n)}

type Address is Data:
  Address{n: Nat, material: P.Material(n), key: Word(Index.width(n))}

def prepend(+anchor: Game.Player, man: P.Man, packed: Packed) -> Packed:
  match man packed:
    case P.Man{owner, kind, square} Packed{n, material, board}:
      Packed{1n+n, P.MaterialCell{P.Descriptor{Bool.not(Three.same(anchor, owner)), kind}, material}, P.Slot{square, board}}

def pack_men(men: List<&2, P.Man>, +anchor: Game.Player, frame: P.Frame) -> Packed:
  match men:
    case Nil{}:
      Packed{0n, Unit{}, frame}
    case head <> tail:
      prepend(anchor, head, pack_men(tail, anchor, frame))

def pack(+anchor: Game.Player, position: P.Position) -> Packed:
  match position:
    case P.Position{turn, wk, bk, men, ep, target}:
      pack_men(men, anchor, P.Frame{anchor, turn, wk, bk, ep, target})

def frame(packed: Packed) -> P.Frame:
  match packed:
    case Packed{n, material, board}:
      P.frame(n, board)

def men(packed: Packed, anchor: Game.Player) -> List<&2, P.Man>:
  match packed:
    case Packed{n, material, board}:
      P.men(n, material, board, anchor)

def unpack(+packed: Packed) -> P.Position:
  +base = frame(packed)
  P.assemble(base, men(packed, P.anchor(base)))

def encode(packed: Packed) -> Address:
  match packed:
    case Packed{+n, material, board}:
      Address{n, material, Index.encode(n, board)}

def decode(address: Address) -> Packed:
  match address:
    case Address{+n, material, key}:
      Packed{n, material, Index.decode(n, key)}

def of_position(anchor: Game.Player, position: P.Position) -> Address:
  encode(pack(anchor, position))

def position(address: Address) -> P.Position:
  unpack(decode(address))
