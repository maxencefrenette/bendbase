import Base
import ./position.bend as P
import ./position_address.bend as Address
import ./position_index.bend as Index
import ./pawnless_chess.bend as Three
import ./game.bend as Game
import ./finite_table.bend as Finite
import ./table_cache.bend as Cache

# Ordered material signatures retain every piece kind and relative owner.
# No fixed material count, promotion family, or table width is built in.
type Named is Data:
  Named{signature: List<&2, P.Descriptor>, entry: Cache.Entry}

def signature(n: Nat, material: P.Material(n)) -> List<&2, P.Descriptor>:
  match n material:
    case 0n Unit{}:
      Nil{}
    case 1n+rest P.MaterialCell{head, tail}:
      head <> signature(rest, tail)

def piece_equal(left: Three.Material, right: Three.Material) -> Bool:
  match left right:
    case Three.Queen{} Three.Queen{}:
      True{}
    case Three.Rook{} Three.Rook{}:
      True{}
    case Three.Bishop{} Three.Bishop{}:
      True{}
    case Three.Knight{} Three.Knight{}:
      True{}
    case _ _:
      False{}

def kind_equal(left: P.PieceKind, right: P.PieceKind) -> Bool:
  match left right:
    case P.Pawn{} P.Pawn{}:
      True{}
    case P.Piece{a} P.Piece{b}:
      piece_equal(a, b)
    case _ _:
      False{}

def bit_equal(left: Bool, right: Bool) -> Bool:
  match left right:
    case False{} False{}:
      True{}
    case True{} True{}:
      True{}
    case _ _:
      False{}

def descriptor_equal(left: P.Descriptor, right: P.Descriptor) -> Bool:
  match left right:
    case P.Descriptor{a, x} P.Descriptor{b, y}:
      bit_equal(a, b) && kind_equal(x, y)

def equal(left: List<&2, P.Descriptor>, right: List<&2, P.Descriptor>) -> Bool:
  match left right:
    case Nil{} Nil{}:
      True{}
    case a <> rest b <> more:
      descriptor_equal(a, b) && equal(rest, more)
    case _ _:
      False{}

def choose(matches: Bool, entry: Cache.Entry, later: Maybe<&2, Cache.Entry>) -> Maybe<&2, Cache.Entry>:
  match matches:
    case True{}:
      Some{entry}
    case False{}:
      later

# First matching entry wins, allowing a newly completed stratum to shadow an
# earlier one. The scheduler still has to establish which stratum is required.
def find(entries: List<&2, Named>, +query: List<&2, P.Descriptor>) -> Maybe<&2, Cache.Entry>:
  match entries:
    case Nil{}:
      None{}
    case Named{name, entry} <> tail:
      choose(equal(query, name), entry, find(tail, query))

def read(width: Nat, key: Word(width), found: Maybe<&2, Cache.Entry>) -> Maybe<&2, Game.Outcome>:
  match found:
    case None{}:
      None{}
    case Some{entry}:
      Cache.lookup(width, key, entry)

def lookup(entries: List<&2, Named>, name: List<&2, P.Descriptor>, width: Nat, key: Word(width)) -> Maybe<&2, Game.Outcome>:
  read(width, key, find(entries, name))

def resolve(entries: List<&2, Named>, address: Address.Address) -> Maybe<&2, Game.Outcome>:
  match address:
    case Address.Address{+n, material, key}:
      lookup(entries, signature(n, material), Index.width(n), key)

def from_family(~D: Data, ~name: D -> List<&2, P.Descriptor>, depth: Nat,
  descriptors: Finite.Table(depth, D), entries: Finite.Table(depth, Cache.Entry), tail: List<&2, Named>) -> List<&2, Named>:
  match depth descriptors entries:
    case 0n descriptor entry:
      Named{name(descriptor), entry} <> tail
    case 1n++rest Finite.Fork{a, b} Finite.Fork{x, y}:
      from_family(~D, ~name, rest, a, x, from_family(~D, ~name, rest, b, y, tail))

# Semantic cache membership, independent of the Boolean matcher.
def Hit(entries: List<&2, Named>, +query: List<&2, P.Descriptor>, +entry: Cache.Entry) -> Type:
  match entries:
    case Nil{}:
      Empty
    case Named{name, value} <> tail:
      ({query == name : List<&2, P.Descriptor>} & {entry == value : Cache.Entry}) | Hit(tail, query, entry)
