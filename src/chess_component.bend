import Base
import ./position.bend as P
import ./game.bend as Game
import ./pawnless_chess.bend as Three
import ./position_address.bend as Address
import ./material_cache.bend as Registry
import ./chess_measure.bend as Measure
import ./position_index.bend as Index

# Components use the same ordered relative-owner signatures as the cache.
# Slot order is retained, including when several men have identical kinds.
type Key is Data:
  Key{stage: Nat, material: List<&2, P.Descriptor>}

def man(anchor: Game.Player, piece: P.Man) -> P.Descriptor:
  match piece:
    case P.Man{owner, kind, square}:
      P.Descriptor{Bool.not(Three.same(anchor, owner)), kind}

def men(+anchor: Game.Player, pieces: List<&2, P.Man>) -> List<&2, P.Descriptor>:
  match pieces:
    case Nil{}:
      Nil{}
    case head <> tail:
      man(anchor, head) <> men(anchor, tail)

def material(anchor: Game.Player, board: P.Position) -> List<&2, P.Descriptor>:
  match board:
    case P.Position{turn, wk, bk, pieces, ep, target}:
      men(anchor, pieces)

def of_position(anchor: Game.Player, +board: P.Position) -> Key:
  Key{Measure.position(board), material(anchor, board)}

def packed_material(packed: Address.Packed) -> List<&2, P.Descriptor>:
  match packed:
    case Address.Packed{n, material, board}:
      Registry.signature(n, material)

def address_material(address: Address.Address) -> List<&2, P.Descriptor>:
  match address:
    case Address.Address{n, material, key}:
      Registry.signature(n, material)

def of_address(+address: Address.Address) -> Key:
  Key{Measure.position(Address.position(address)), address_material(address)}

def width(key: Key) -> Nat:
  match key:
    case Key{stage, material}:
      Index.width(List.length(&2, P.Descriptor, material))

def address_width(address: Address.Address) -> Nat:
  match address:
    case Address.Address{n, material, key}:
      Index.width(n)
