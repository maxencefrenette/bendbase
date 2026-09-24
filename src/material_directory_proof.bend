import Base
import ./material_directory.bend as D
import ./position.bend as P
import ./pawnless_chess.bend as Chess
import ./chess_measure.bend as M
import ./material_cache.bend as Registry
import ./material_cache_proof.bend as RegistryProof
import ./table_cache.bend as Cache
import ./game.bend as Game
import ./finite_table.bend as Finite
import ./chess_selection_proof.bend as Selection
import ./component_cache.bend as Stages
import ./chess_cache_proof.bend as CacheProof
import ./table_cache_proof.bend as TableProof
import ./position_address.bend as Address
import ./position_index.bend as Index
import ./chess_component.bend as Component
import ./chess_component_proof.bend as ComponentProof
import ./chess_measure_proof.bend as MeasureProof
import ./chess_graph.bend as Graph
import ./chess.bend as CommonChess
import ./chess_cache.bend as ChessCache

def append_left(-A: Data, +value: A, +left: List<&2, A>, +right: List<&2, A>, member: D.Member(A, value, left)) ->
  D.Member(A, value, List.append(&2, A, left, right)):
  match left member:
    case Nil{} member:
      match member:
    case head <> tail Inl{same}:
      Inl{same}
    case head <> tail Inr{later}:
      Inr{append_left(A, value, tail, right, later)}

def append_right(-A: Data, +value: A, +left: List<&2, A>, +right: List<&2, A>, member: D.Member(A, value, right)) ->
  D.Member(A, value, List.append(&2, A, left, right)):
  match left:
    case Nil{}:
      member
    case head <> tail:
      Inr{append_right(A, value, tail, right, member)}

def descriptor(+value: P.Descriptor) -> D.Member(P.Descriptor, value, D.descriptors()):
  match value:
    case P.Descriptor{False{}, P.Pawn{}}:
      Inl{{==}}
    case P.Descriptor{False{}, P.Piece{Chess.Queen{}}}:
      Inr{Inl{{==}}}
    case P.Descriptor{False{}, P.Piece{Chess.Rook{}}}:
      Inr{Inr{Inl{{==}}}}
    case P.Descriptor{False{}, P.Piece{Chess.Bishop{}}}:
      Inr{Inr{Inr{Inl{{==}}}}}
    case P.Descriptor{False{}, P.Piece{Chess.Knight{}}}:
      Inr{Inr{Inr{Inr{Inl{{==}}}}}}
    case P.Descriptor{True{}, P.Pawn{}}:
      Inr{Inr{Inr{Inr{Inr{Inl{{==}}}}}}}
    case P.Descriptor{True{}, P.Piece{Chess.Queen{}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inl{{==}}}}}}}}
    case P.Descriptor{True{}, P.Piece{Chess.Rook{}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inl{{==}}}}}}}}}
    case P.Descriptor{True{}, P.Piece{Chess.Bishop{}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inl{{==}}}}}}}}}}
    case P.Descriptor{True{}, P.Piece{Chess.Knight{}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inl{{==}}}}}}}}}}}

def prefix(+head: P.Descriptor, +tail: List<&2, P.Descriptor>, +tails: List<&2, List<&2, P.Descriptor>>,
  member: D.Member(List<&2, P.Descriptor>, tail, tails)) -> D.Member(List<&2, P.Descriptor>, head <> tail, D.prefix(head, tails)):
  match tails member:
    case Nil{} member:
      match member:
    case first <> rest Inl{same}:
      Inl{Equal.cong(List<&2, P.Descriptor>, List<&2, P.Descriptor>, value => head <> value, tail, first, same)}
    case first <> rest Inr{later}:
      Inr{prefix(head, tail, rest, later)}

def products(+head: P.Descriptor, +tail: List<&2, P.Descriptor>, +heads: List<&2, P.Descriptor>, +tails: List<&2, List<&2, P.Descriptor>>,
  first: D.Member(P.Descriptor, head, heads), rest: D.Member(List<&2, P.Descriptor>, tail, tails)) ->
  D.Member(List<&2, P.Descriptor>, head <> tail, D.products(heads, tails)):
  match heads first:
    case Nil{} first:
      match first:
    case +item <> +more Inl{same}:
      %same : D.Member(List<&2, P.Descriptor>, head <> tail, List.append(&2, List<&2, P.Descriptor>, D.prefix(_, tails), D.products(more, tails)))
      append_left(List<&2, P.Descriptor>, head <> tail, D.prefix(head, tails), D.products(more, tails), prefix(head, tail, tails, rest))
    case item <> more Inr{later}:
      append_right(List<&2, P.Descriptor>, head <> tail, D.prefix(item, tails), D.products(more, tails), products(head, tail, more, tails, later, rest))

def names(+capacity: Nat, +query: List<&2, P.Descriptor>, bounded: M.Le(List.length(&2, P.Descriptor, query), capacity)) ->
  D.Member(List<&2, P.Descriptor>, query, D.names(capacity)):
  match capacity query:
    case 0n Nil{}:
      Inl{{==}}
    case 0n head <> tail:
      match bounded:
    case 1n+rest Nil{}:
      Inl{{==}}
    case 1n+rest head <> tail:
      Inr{products(head, tail, D.descriptors(), D.names(rest), descriptor(head), names(rest, tail, bounded))}

def matches(+query: List<&2, P.Descriptor>, +name: List<&2, P.Descriptor>, same: {query == name : List<&2, P.Descriptor>}) -> Game.Truth(Registry.equal(query, name)):
  %same : Game.Truth(Registry.equal(query, _))
  %Equal.sym(Bool, Registry.equal(query, query), True{}, RegistryProof.refl(query)) : Game.Truth(_)
  Unit{}

def skip(+query: List<&2, P.Descriptor>, +name: List<&2, P.Descriptor>, +tail: List<&2, List<&2, P.Descriptor>>,
  no: Game.Truth(Bool.not(Registry.equal(query, name))), member: D.Member(List<&2, P.Descriptor>, query, name <> tail)) -> D.Member(List<&2, P.Descriptor>, query, tail):
  match member:
    case Inl{same}:
      Selection.contradiction(D.Member(List<&2, P.Descriptor>, query, tail), Registry.equal(query, name), matches(query, name, same), no)
    case Inr{later}:
      later

def head(~C: Data, ~solve: @+name: List<&2, P.Descriptor> -> C -> Finite.Table(D.width(name), Game.Outcome),
  +query: List<&2, P.Descriptor>, +name: List<&2, P.Descriptor>, +context: C, +tail: List<&2, Registry.Named>,
  +yes: Game.Truth(Registry.equal(query, name))) ->
  {Registry.find(Registry.Named{name, D.entry(~C, ~solve, name, context)} <> tail, query) == Some{D.entry(~C, ~solve, query, context)} : Maybe<&2, Cache.Entry>}:
  %Equal.sym(Bool, Registry.equal(query, name), True{}, Selection.yes_equal(Registry.equal(query, name), yes)) :
    {Registry.choose(_, D.entry(~C, ~solve, name, context), Registry.find(tail, query)) == Some{D.entry(~C, ~solve, query, context)} : Maybe<&2, Cache.Entry>}
  Equal.cong(List<&2, P.Descriptor>, Maybe<&2, Cache.Entry>, value => Some{D.entry(~C, ~solve, value, context)}, name, query,
    Equal.sym(List<&2, P.Descriptor>, query, name, RegistryProof.reflect(query, name, yes)))

def later(+query: List<&2, P.Descriptor>, +name: List<&2, P.Descriptor>, +entry: Cache.Entry, +tail: List<&2, Registry.Named>,
  +expected: Cache.Entry, no: Game.Truth(Bool.not(Registry.equal(query, name))),
  found: {Registry.find(tail, query) == Some{expected} : Maybe<&2, Cache.Entry>}) ->
  {Registry.find(Registry.Named{name, entry} <> tail, query) == Some{expected} : Maybe<&2, Cache.Entry>}:
  %Equal.sym(Bool, Registry.equal(query, name), False{}, Selection.no_equal(Registry.equal(query, name), no)) :
    {Registry.choose(_, entry, Registry.find(tail, query)) == Some{expected} : Maybe<&2, Cache.Entry>}
  found

def register(~C: Data, ~solve: @+name: List<&2, P.Descriptor> -> C -> Finite.Table(D.width(name), Game.Outcome),
  +catalog: List<&2, List<&2, P.Descriptor>>, +query: List<&2, P.Descriptor>, +context: C,
  member: D.Member(List<&2, P.Descriptor>, query, catalog)) ->
  {Registry.find(D.register(~C, ~solve, catalog, context), query) == Some{D.entry(~C, ~solve, query, context)} : Maybe<&2, Cache.Entry>}:
  match catalog:
    case Nil{}:
      match member:
    case +name <> +tail:
      Selection.split(
        {Registry.find(D.register(~C, ~solve, catalog, context), query) == Some{D.entry(~C, ~solve, query, context)} : Maybe<&2, Cache.Entry>},
        Registry.equal(query, name), yes => head(~C, ~solve, query, name, context, D.register(~C, ~solve, tail, context), yes),
        +no => later(query, name, D.entry(~C, ~solve, name, context), D.register(~C, ~solve, tail, context), D.entry(~C, ~solve, query, context), no,
          register(~C, ~solve, tail, query, context, skip(query, name, tail, no, member))))

def build(~C: Data, ~solve: @+name: List<&2, P.Descriptor> -> C -> Finite.Table(D.width(name), Game.Outcome),
  +capacity: Nat, +query: List<&2, P.Descriptor>, +context: C, bounded: M.Le(List.length(&2, P.Descriptor, query), capacity)) ->
  {Registry.find(D.build(~C, ~solve, capacity, context), query) == Some{D.entry(~C, ~solve, query, context)} : Maybe<&2, Cache.Entry>}:
  register(~C, ~solve, D.names(capacity), query, context, names(capacity, query, bounded))

def stage(~C: Data,
  ~solve: @+name: List<&2, P.Descriptor> -> Nat -> C -> List<&2, Stages.Stage> -> Finite.Table(D.width(name), Game.Outcome),
  +index: Nat, +capacity: Nat, +context: C, +previous: List<&2, Stages.Stage>, +name: List<&2, P.Descriptor>,
  bounded: M.Le(List.length(&2, P.Descriptor, name), capacity)) ->
  {Registry.find(D.stage(~C, ~solve, index, capacity, context, previous), name) ==
    Some{Cache.Entry{D.width(name), solve(name, index, context, previous)}} : Maybe<&2, Cache.Entry>}:
  build(~D.Work<C>, ~(+name => work => D.solve_work(~C, ~solve, name, work)), capacity, name, D.Work{index, context, previous}, bounded)

def available_later(+query: Nat, +index: Nat, +entries: List<&2, Registry.Named>, +tail: List<&2, Stages.Stage>, +name: List<&2, P.Descriptor>,
  no: Game.Truth(Bool.not(Stages.equal(query, index))), available: D.Available(tail, query, name)) ->
  D.Available(Stages.Stage{index, entries} <> tail, query, name):
  match available:
    case Tuple{+table, found}:
      (table,
        Equal.trans(Maybe<&2, Cache.Entry>, Stages.select(Stages.Stage{index, entries} <> tail, query, name), Stages.select(tail, query, name),
          Some{Cache.Entry{D.width(name), table}},
          Equal.cong(Bool, Maybe<&2, Cache.Entry>, matches => Stages.in_stage(Stages.choose(matches, entries, Stages.find(tail, query)), name),
            Stages.equal(query, index), False{}, Selection.no_equal(Stages.equal(query, index), no)), found))

def available_here(~C: Data,
  ~solve: @+name: List<&2, P.Descriptor> -> Nat -> C -> List<&2, Stages.Stage> -> Finite.Table(D.width(name), Game.Outcome),
  +query: Nat, +index: Nat, +capacity: Nat, +context: C, +tail: List<&2, Stages.Stage>, +name: List<&2, P.Descriptor>,
  yes: Game.Truth(Stages.equal(query, index)), bounded: M.Le(List.length(&2, P.Descriptor, name), capacity)) ->
  D.Available(Stages.Stage{index, D.stage(~C, ~solve, index, capacity, context, tail)} <> tail, query, name):
  (solve(name, index, context, tail),
    Equal.trans(Maybe<&2, Cache.Entry>,
      Stages.select(Stages.Stage{index, D.stage(~C, ~solve, index, capacity, context, tail)} <> tail, query, name),
      Registry.find(D.stage(~C, ~solve, index, capacity, context, tail), name), Some{Cache.Entry{D.width(name), solve(name, index, context, tail)}},
      Equal.cong(Bool, Maybe<&2, Cache.Entry>, matches => Stages.in_stage(Stages.choose(matches, D.stage(~C, ~solve, index, capacity, context, tail), Stages.find(tail, query)), name),
        Stages.equal(query, index), True{}, Selection.yes_equal(Stages.equal(query, index), yes)),
      stage(~C, ~solve, index, capacity, context, tail, name, bounded)))

def matches_true(+b: Bool, same: {b == True{} : Bool}) -> Game.Truth(b):
  %Equal.sym(Bool, b, True{}, same) : Game.Truth(_)
  Unit{}

def matches_false(+b: Bool, same: {b == False{} : Bool}) -> Game.Truth(Bool.not(b)):
  %Equal.sym(Bool, b, False{}, same) : Game.Truth(Bool.not(_))
  Unit{}

def schedule_step(~C: Data,
  ~solve: @+name: List<&2, P.Descriptor> -> Nat -> C -> List<&2, Stages.Stage> -> Finite.Table(D.width(name), Game.Outcome),
  +same: Bool, +prior: Nat, +query: Nat, +capacity: Nat, +context: C, +name: List<&2, P.Descriptor>,
  equal: {Stages.equal(1n+query, 1n+prior) == same : Bool}, bounded: M.Le(1n+query, 1n+prior), material: M.Le(List.length(&2, P.Descriptor, name), capacity),
  recurse: M.Le(1n+query, prior) -> M.Le(List.length(&2, P.Descriptor, name), capacity) -> D.Available(D.schedule(~C, ~solve, prior, capacity, context), 1n+query, name)) ->
  D.Available(D.schedule(~C, ~solve, 1n+prior, capacity, context), 1n+query, name):
  match same:
    case True{}:
      available_here(~C, ~solve, 1n+query, 1n+prior, capacity, context, D.schedule(~C, ~solve, prior, capacity, context), name,
        matches_true(Stages.equal(1n+query, 1n+prior), equal), material)
    case False{}:
      +no = matches_false(Stages.equal(1n+query, 1n+prior), equal)
      available_later(1n+query, 1n+prior,
        D.stage(~C, ~solve, 1n+prior, capacity, context, D.schedule(~C, ~solve, prior, capacity, context)), D.schedule(~C, ~solve, prior, capacity, context), name, no,
        recurse(CacheProof.tighten(1n+query, 1n+prior, bounded, no))(material))

def schedule(~C: Data,
  ~solve: @+name: List<&2, P.Descriptor> -> Nat -> C -> List<&2, Stages.Stage> -> Finite.Table(D.width(name), Game.Outcome),
  +count: Nat, +query: Nat, +capacity: Nat, +context: C, +name: List<&2, P.Descriptor>,
  bounded: M.Le(1n+query, count), material: M.Le(List.length(&2, P.Descriptor, name), capacity)) ->
  D.Available(D.schedule(~C, ~solve, count, capacity, context), 1n+query, name):
  match count:
    case 0n:
      match bounded:
    case 1n++prior:
      schedule_step(~C, ~solve, Stages.equal(1n+query, 1n+prior), prior, query, capacity, context, name, {==}, bounded, material,
        earlier => fits => schedule(~C, ~solve, prior, query, capacity, context, name, earlier, fits))

def read_select(+found: Maybe<&2, List<&2, Registry.Named>>, +n: Nat, +material: P.Material(n), +key: Word(Index.width(n))) ->
  {Stages.read(found, Address.Address{n, material, key}) == Registry.read(Index.width(n), key, Stages.in_stage(found, Registry.signature(n, material))) : Maybe<&2, Game.Outcome>}:
  match found:
    case None{}:
      {==}
    case Some{entries}:
      {==}

def lookup_format(+stored: Nat, +queried: Nat, +table: Finite.Table(stored, Game.Outcome), format: {queried == stored : Nat}) ->
  @key: Word(queried) -> &value: Game.Outcome -> {Cache.lookup(queried, key, Cache.Entry{stored, table}) == Some{value} : Maybe<&2, Game.Outcome>}:
  %Equal.sym(Nat, queried, stored, format) :
    @key: Word(_) -> &value: Game.Outcome -> {Cache.lookup(_, key, Cache.Entry{stored, table}) == Some{value} : Maybe<&2, Game.Outcome>}
  +key => (Finite.get(stored, Game.Outcome, key, table), TableProof.exact(stored, key, table))

def selected_value(+stages: List<&2, Stages.Stage>, +index: Nat, +n: Nat, +material: P.Material(n), +key: Word(Index.width(n)),
  +table: Finite.Table(D.width(Registry.signature(n, material)), Game.Outcome),
  found: {Stages.select(stages, index, Registry.signature(n, material)) == Some{Cache.Entry{D.width(Registry.signature(n, material)), table}} : Maybe<&2, Cache.Entry>}) ->
  &value: Game.Outcome -> {Stages.resolve(stages, index, Address.Address{n, material, key}) == Some{value} : Maybe<&2, Game.Outcome>}:
  %Equal.sym(Maybe<&2, Game.Outcome>, Stages.resolve(stages, index, Address.Address{n, material, key}),
    Registry.read(Index.width(n), key, Stages.select(stages, index, Registry.signature(n, material))),
    read_select(Stages.find(stages, index), n, material, key)) : &value: Game.Outcome -> {_ == Some{value} : Maybe<&2, Game.Outcome>}
  %Equal.sym(Maybe<&2, Cache.Entry>, Stages.select(stages, index, Registry.signature(n, material)),
    Some{Cache.Entry{D.width(Registry.signature(n, material)), table}}, found) :
    &value: Game.Outcome -> {Registry.read(Index.width(n), key, _) == Some{value} : Maybe<&2, Game.Outcome>}
  lookup_format(D.width(Registry.signature(n, material)), Index.width(n), table, ComponentProof.width_agrees(Address.Address{n, material, key}))(key)

def available_value(+stages: List<&2, Stages.Stage>, +index: Nat, +address: Address.Address,
  available: D.Available(stages, index, Component.address_material(address))) ->
  &value: Game.Outcome -> {Stages.resolve(stages, index, address) == Some{value} : Maybe<&2, Game.Outcome>}:
  match address available:
    case Address.Address{n, material, key} Tuple{table, found}:
      selected_value(stages, index, n, material, key, table, found)

def earlier_available(~C: Data,
  ~solve: @+name: List<&2, P.Descriptor> -> Nat -> C -> List<&2, Stages.Stage> -> Finite.Table(D.width(name), Game.Outcome),
  +count: Nat, +capacity: Nat, +context: C, +target: P.Position, +current: Nat, +name: List<&2, P.Descriptor>,
  earlier: M.Lt(M.position(target), current), bounded: M.Le(current, 1n+count), material: M.Le(List.length(&2, P.Descriptor, name), capacity)) ->
  D.Available(D.schedule(~C, ~solve, count, capacity, context), M.position(target), name):
  match target:
    case P.Position{turn, wk, bk, pieces, ep, square}:
      schedule(~C, ~solve, count, 1n+M.men(pieces), capacity, context, name,
        MeasureProof.trans(1n+M.position(target), current, 1n+count, earlier, bounded), material)

# No stage-registration or material-registration premise remains. The caller
# supplies only bounds on the completed stages and SOURCE material size.
# The arbitrary solver's values are NOT asserted to be correct WDL here.
def reset_resolves(~C: Data,
  ~solve: @+name: List<&2, P.Descriptor> -> Nat -> C -> List<&2, Stages.Stage> -> Finite.Table(D.width(name), Game.Outcome),
  +count: Nat, +capacity: Nat, +context: C, +anchor: Game.Player, +board: P.Position, +move: CommonChess.Action,
  legal: Game.Truth(CommonChess.legal(board, move)), reset: Game.Truth(CommonChess.resets(board, move)), bounded: M.Le(M.position(board), 1n+count),
  material: M.Le(List.length(&2, P.Descriptor, Component.material(anchor, board)), capacity)) ->
  &value: Game.Outcome -> {ChessCache.resolve(D.schedule(~C, ~solve, count, capacity, context), Graph.address(Graph.route(anchor, board, move))) == Some{value} : Maybe<&2, Game.Outcome>}:
  +address = Graph.address(Graph.route(anchor, board, move))
  available_value(D.schedule(~C, ~solve, count, capacity, context), M.position(Address.position(address)), address,
    earlier_available(~C, ~solve, count, capacity, context, Address.position(address), M.position(board), Component.address_material(address),
      CacheProof.routed_stage(anchor, board, move, legal, reset), bounded,
      MeasureProof.trans(List.length(&2, P.Descriptor, Component.address_material(address)),
        List.length(&2, P.Descriptor, Component.material(anchor, board)), capacity, ComponentProof.routed_material_count(anchor, board, move), material)))
