import Base
import ./position.bend as P
import ./pawnless_chess.bend as Three
import ./game.bend as Game
import ./game_proof.bend as Logic
import ./dependency_engine.bend as Dependencies
import ./finite_table.bend as Finite
import ./table_cache.bend as Cache
import ./table_cache_proof.bend as CacheProof
import ./material_cache.bend as Registry
import ./position_address.bend as Address
import ./position_index.bend as Index

def and_left(+a: Bool, b: Bool, evidence: Game.Truth(a && b)) -> Game.Truth(a):
  match a:
    case False{}:
      match evidence:
    case True{}:
      Unit{}

def and_right(a: Bool, +b: Bool, evidence: Game.Truth(a && b)) -> Game.Truth(b):
  match a:
    case False{}:
      match evidence:
    case True{}:
      evidence

def bit_reflect(+a: Bool, +b: Bool, evidence: Game.Truth(Registry.bit_equal(a, b))) -> {a == b : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case True{} True{}:
      {==}
    case False{} True{}:
      match evidence:
    case True{} False{}:
      match evidence:

def piece_reflect(+a: Three.Material, +b: Three.Material, evidence: Game.Truth(Registry.piece_equal(a, b))) ->
  {a == b : Three.Material}:
  match a b:
    case Three.Queen{} Three.Queen{}:
      {==}
    case Three.Queen{} Three.Rook{}:
      match evidence:
    case Three.Queen{} Three.Bishop{}:
      match evidence:
    case Three.Queen{} Three.Knight{}:
      match evidence:
    case Three.Rook{} Three.Queen{}:
      match evidence:
    case Three.Rook{} Three.Rook{}:
      {==}
    case Three.Rook{} Three.Bishop{}:
      match evidence:
    case Three.Rook{} Three.Knight{}:
      match evidence:
    case Three.Bishop{} Three.Queen{}:
      match evidence:
    case Three.Bishop{} Three.Rook{}:
      match evidence:
    case Three.Bishop{} Three.Bishop{}:
      {==}
    case Three.Bishop{} Three.Knight{}:
      match evidence:
    case Three.Knight{} Three.Queen{}:
      match evidence:
    case Three.Knight{} Three.Rook{}:
      match evidence:
    case Three.Knight{} Three.Bishop{}:
      match evidence:
    case Three.Knight{} Three.Knight{}:
      {==}

def kind_reflect(+a: P.PieceKind, +b: P.PieceKind, evidence: Game.Truth(Registry.kind_equal(a, b))) ->
  {a == b : P.PieceKind}:
  match a b:
    case P.Pawn{} P.Pawn{}:
      {==}
    case P.Pawn{} P.Piece{kind}:
      match evidence:
    case P.Piece{kind} P.Pawn{}:
      match evidence:
    case P.Piece{x} P.Piece{y}:
      Equal.cong(Three.Material, P.PieceKind, kind => P.Piece{kind}, x, y, piece_reflect(x, y, evidence))

def descriptor_reflect(+a: P.Descriptor, +b: P.Descriptor, +evidence: Game.Truth(Registry.descriptor_equal(a, b))) ->
  {a == b : P.Descriptor}:
  match a b:
    case P.Descriptor{x, p} P.Descriptor{y, q}:
      %bit_reflect(x, y, and_left(Registry.bit_equal(x, y), Registry.kind_equal(p, q), evidence)) :
        {P.Descriptor{x, p} == P.Descriptor{_, q} : P.Descriptor}
      %kind_reflect(p, q, and_right(Registry.bit_equal(x, y), Registry.kind_equal(p, q), evidence)) :
        {P.Descriptor{x, p} == P.Descriptor{x, _} : P.Descriptor}
      {==}

def reflect(+left: List<&2, P.Descriptor>, +right: List<&2, P.Descriptor>, +evidence: Game.Truth(Registry.equal(left, right))) ->
  {left == right : List<&2, P.Descriptor>}:
  match left right:
    case Nil{} Nil{}:
      {==}
    case Nil{} head <> tail:
      match evidence:
    case head <> tail Nil{}:
      match evidence:
    case a <> rest b <> more:
      %descriptor_reflect(a, b, and_left(Registry.descriptor_equal(a, b), Registry.equal(rest, more), evidence)) :
        {a <> rest == _ <> more : List<&2, P.Descriptor>}
      %reflect(rest, more, and_right(Registry.descriptor_equal(a, b), Registry.equal(rest, more), evidence)) :
        {a <> rest == a <> _ : List<&2, P.Descriptor>}
      {==}

def bit_refl(+bit: Bool) -> {Registry.bit_equal(bit, bit) == True{} : Bool}:
  match bit:
    case False{}:
      {==}
    case True{}:
      {==}

def piece_refl(+kind: Three.Material) -> {Registry.piece_equal(kind, kind) == True{} : Bool}:
  match kind:
    case Three.Queen{}:
      {==}
    case Three.Rook{}:
      {==}
    case Three.Bishop{}:
      {==}
    case Three.Knight{}:
      {==}

def kind_refl(+kind: P.PieceKind) -> {Registry.kind_equal(kind, kind) == True{} : Bool}:
  match kind:
    case P.Pawn{}:
      {==}
    case P.Piece{piece}:
      piece_refl(piece)

def descriptor_refl(+descriptor: P.Descriptor) -> {Registry.descriptor_equal(descriptor, descriptor) == True{} : Bool}:
  match descriptor:
    case P.Descriptor{bit, kind}:
      %Equal.sym(Bool, Registry.bit_equal(bit, bit), True{}, bit_refl(bit)) :
        {_ && Registry.kind_equal(kind, kind) == True{} : Bool}
      kind_refl(kind)

def refl(+signature: List<&2, P.Descriptor>) -> {Registry.equal(signature, signature) == True{} : Bool}:
  match signature:
    case Nil{}:
      {==}
    case head <> tail:
      %Equal.sym(Bool, Registry.descriptor_equal(head, head), True{}, descriptor_refl(head)) :
        {_ && Registry.equal(tail, tail) == True{} : Bool}
      refl(tail)

def find_head(+signature: List<&2, P.Descriptor>, +entry: Cache.Entry, +tail: List<&2, Registry.Named>) ->
  {Registry.find(Registry.Named{signature, entry} <> tail, signature) == Some{entry} : Maybe<&2, Cache.Entry>}:
  %Equal.sym(Bool, Registry.equal(signature, signature), True{}, refl(signature)) :
    {Registry.choose(_, entry, Registry.find(tail, signature)) == Some{entry} : Maybe<&2, Cache.Entry>}
  {==}

def resolve_head(+n: Nat, +material: P.Material(n), +key: Word(Index.width(n)),
  +table: Finite.Table(Index.width(n), Game.Outcome), +tail: List<&2, Registry.Named>) ->
  {Registry.resolve(Registry.Named{Registry.signature(n, material), Cache.Entry{Index.width(n), table}} <> tail,
     Address.Address{n, material, key}) == Some{Finite.get(Index.width(n), Game.Outcome, key, table)} : Maybe<&2, Game.Outcome>}:
  %Equal.sym(Maybe<&2, Cache.Entry>,
    Registry.find(Registry.Named{Registry.signature(n, material), Cache.Entry{Index.width(n), table}} <> tail, Registry.signature(n, material)),
    Some{Cache.Entry{Index.width(n), table}},
    find_head(Registry.signature(n, material), Cache.Entry{Index.width(n), table}, tail)) :
    {Registry.read(Index.width(n), key, _) == Some{Finite.get(Index.width(n), Game.Outcome, key, table)} : Maybe<&2, Game.Outcome>}
  CacheProof.exact(Index.width(n), key, table)

def choice_sound(+matches: Bool, +value: Cache.Entry, +later: Maybe<&2, Cache.Entry>, +entry: Cache.Entry,
  found: {Registry.choose(matches, value, later) == Some{entry} : Maybe<&2, Cache.Entry>}) ->
  (Game.Truth(matches) & {entry == value : Cache.Entry}) | {later == Some{entry} : Maybe<&2, Cache.Entry>}:
  match matches:
    case True{}:
      Inl{(Unit{}, Equal.sym(Cache.Entry, value, entry,
        Equal.cong(Maybe<&2, Cache.Entry>, Cache.Entry, result => Dependencies.or_else(Cache.Entry, value, result),
          Some{value}, Some{entry}, found)))}
    case False{}:
      Inr{found}

def head_sound(+query: List<&2, P.Descriptor>, +name: List<&2, P.Descriptor>, +value: Cache.Entry, +entry: Cache.Entry,
  evidence: Game.Truth(Registry.equal(query, name)) & {entry == value : Cache.Entry}) ->
  {query == name : List<&2, P.Descriptor>} & {entry == value : Cache.Entry}:
  match evidence:
    case Tuple{matches, same}:
      (reflect(query, name, matches), same)

def present_entry(found: Maybe<&2, Cache.Entry>) -> Type:
  match found:
    case None{}:
      Empty
    case Some{entry}:
      Unit

def none_entry(+entry: Cache.Entry, found: {None{} == Some{entry} : Maybe<&2, Cache.Entry>}) -> Empty:
  %Equal.sym(Maybe<&2, Cache.Entry>, None{}, Some{entry}, found) : present_entry(_)
  Unit{}

def find_sound(+entries: List<&2, Registry.Named>, +query: List<&2, P.Descriptor>, +entry: Cache.Entry,
  found: {Registry.find(entries, query) == Some{entry} : Maybe<&2, Cache.Entry>}) -> Registry.Hit(entries, query, entry):
  match entries:
    case Nil{}:
      none_entry(entry, found)
    case Registry.Named{name, value} <> tail:
      Logic.or_map(
        Game.Truth(Registry.equal(query, name)) & {entry == value : Cache.Entry},
        {Registry.find(tail, query) == Some{entry} : Maybe<&2, Cache.Entry>},
        {query == name : List<&2, P.Descriptor>} & {entry == value : Cache.Entry},
        Registry.Hit(tail, query, entry),
        choice_sound(Registry.equal(query, name), value, Registry.find(tail, query), entry, found),
        evidence => head_sound(query, name, value, entry, evidence),
        evidence => find_sound(tail, query, entry, evidence))
