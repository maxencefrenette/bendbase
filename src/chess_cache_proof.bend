import Base
import ./chess_cache.bend as Cache
import ./component_cache.bend as Stages
import ./material_cache.bend as Registry
import ./table_cache.bend as Tables
import ./table_cache_proof.bend as TableProof
import ./position.bend as P
import ./position_address.bend as Address
import ./position_index.bend as Index
import ./game.bend as Game
import ./finite_table.bend as Finite
import ./clock_solver.bend as Solver
import ./chess_measure.bend as M
import ./chess_selection_proof.bend as Selection
import ./chess_graph.bend as Graph
import ./chess_graph_proof.bend as GraphProof
import ./chess.bend as Chess
import ./chess_measure_proof.bend as MeasureProof

# This proves stage coverage of the ACTUAL scheduler, without assuming a
# successful stage lookup. Material-directory coverage is a separate obligation.
def tighten(+a: Nat, +b: Nat, bounded: M.Le(a, b), different: Game.Truth(Bool.not(Stages.equal(a, b)))) -> M.Lt(a, b):
  match a b:
    case 0n 0n:
      match different:
    case 0n 1n+rest:
      Unit{}
    case 1n+rest 0n:
      match bounded:
    case 1n+x 1n+y:
      tighten(x, y, bounded, different)

def found_here(+query: Nat, +index: Nat, +entries: List<&2, Registry.Named>, +tail: List<&2, Stages.Stage>,
  same: Game.Truth(Stages.equal(query, index))) ->
  &directory: List<&2, Registry.Named> -> {Stages.find(Stages.Stage{index, entries} <> tail, query) == Some{directory} : Maybe<&2, List<&2, Registry.Named>>}:
  (entries,
    Equal.cong(Bool, Maybe<&2, List<&2, Registry.Named>>, matches => Stages.choose(matches, entries, Stages.find(tail, query)),
      Stages.equal(query, index), True{}, Selection.yes_equal(Stages.equal(query, index), same)))

def found_later(+query: Nat, +index: Nat, +entries: List<&2, Registry.Named>, +tail: List<&2, Stages.Stage>,
  different: Game.Truth(Bool.not(Stages.equal(query, index))),
  found: &directory: List<&2, Registry.Named> -> {Stages.find(tail, query) == Some{directory} : Maybe<&2, List<&2, Registry.Named>>}) ->
  &directory: List<&2, Registry.Named> -> {Stages.find(Stages.Stage{index, entries} <> tail, query) == Some{directory} : Maybe<&2, List<&2, Registry.Named>>}:
  match found:
    case Tuple{+directory, equality}:
      (directory, Equal.trans(Maybe<&2, List<&2, Registry.Named>>,
        Stages.find(Stages.Stage{index, entries} <> tail, query), Stages.find(tail, query), Some{directory},
        Equal.cong(Bool, Maybe<&2, List<&2, Registry.Named>>, matches => Stages.choose(matches, entries, Stages.find(tail, query)),
          Stages.equal(query, index), False{}, Selection.no_equal(Stages.equal(query, index), different)), equality))

def schedule_found(~C: Nat -> Data,
  ~build: @+stage: Nat -> @+width: Nat -> C(width) -> List<&2, Stages.Stage> -> List<&2, Registry.Named>,
  +count: Nat, +query: Nat, +width: Nat, +context: C(width), bounded: M.Le(1n+query, count)) ->
  &directory: List<&2, Registry.Named> ->
    {Stages.find(Stages.schedule(~C, ~build, count, width, context), 1n+query) == Some{directory} : Maybe<&2, List<&2, Registry.Named>>}:
  match count:
    case 0n:
      match bounded:
    case 1n++prior:
      +tail = Stages.schedule(~C, ~build, prior, width, context)
      +entries = build(1n+prior, width, context, tail)
      Selection.split(
        (&directory: List<&2, Registry.Named> -> {Stages.find(Stages.Stage{1n+prior, entries} <> tail, 1n+query) == Some{directory} : Maybe<&2, List<&2, Registry.Named>>}),
        Stages.equal(1n+query, 1n+prior),
        same => found_here(1n+query, 1n+prior, entries, tail, same),
        +different => found_later(1n+query, 1n+prior, entries, tail, different,
          schedule_found(~C, ~build, prior, query, width, context, tighten(1n+query, 1n+prior, bounded, different))))

# Exact value reads for any stage/directory location, not just the cache head.
# The premises identify the registered table; they do not assert its WDL
# correctness. That semantic invariant must come from the component induction.
def registered(+stages: List<&2, Stages.Stage>, +n: Nat, +material: P.Material(n), +key: Word(Index.width(n)),
  +directory: List<&2, Registry.Named>, +table: Finite.Table(Index.width(n), Game.Outcome),
  stage: {Stages.find(stages, M.position(Address.position(Address.Address{n, material, key}))) == Some{directory} : Maybe<&2, List<&2, Registry.Named>>},
  entry: {Registry.find(directory, Registry.signature(n, material)) == Some{Tables.Entry{Index.width(n), table}} : Maybe<&2, Tables.Entry>}) ->
  {Cache.resolve(stages, Address.Address{n, material, key}) == Some{Finite.get(Index.width(n), Game.Outcome, key, table)} : Maybe<&2, Game.Outcome>}:
  %Equal.sym(Maybe<&2, List<&2, Registry.Named>>, Stages.find(stages, M.position(Address.position(Address.Address{n, material, key}))), Some{directory}, stage) :
    {Stages.read(_, Address.Address{n, material, key}) == Some{Finite.get(Index.width(n), Game.Outcome, key, table)} : Maybe<&2, Game.Outcome>}
  %Equal.sym(Maybe<&2, Tables.Entry>, Registry.find(directory, Registry.signature(n, material)), Some{Tables.Entry{Index.width(n), table}}, entry) :
    {Registry.read(Index.width(n), key, _) == Some{Finite.get(Index.width(n), Game.Outcome, key, table)} : Maybe<&2, Game.Outcome>}
  TableProof.exact(Index.width(n), key, table)

def reset_registered(+width: Nat, +stages: List<&2, Stages.Stage>, +n: Nat, +material: P.Material(n), +key: Word(Index.width(n)),
  +directory: List<&2, Registry.Named>, +table: Finite.Table(Index.width(n), Game.Outcome),
  stage: {Stages.find(stages, M.position(Address.position(Address.Address{n, material, key}))) == Some{directory} : Maybe<&2, List<&2, Registry.Named>>},
  entry: {Registry.find(directory, Registry.signature(n, material)) == Some{Tables.Entry{Index.width(n), table}} : Maybe<&2, Tables.Entry>}) ->
  {Cache.reset(width, stages, Address.Address{n, material, key}) == Some{Solver.Reset{Finite.get(Index.width(n), Game.Outcome, key, table)}} : Maybe<&2, Solver.Edge<width>>}:
  Equal.cong(Maybe<&2, Game.Outcome>, Maybe<&2, Solver.Edge<width>>, value => Cache.reset_value(width, value),
    Cache.resolve(stages, Address.Address{n, material, key}), Some{Finite.get(Index.width(n), Game.Outcome, key, table)},
    registered(stages, n, material, key, directory, table, stage, entry))

def routed_stage(+anchor: Game.Player, +board: P.Position, +move: Chess.Action,
  legal: Game.Truth(Chess.legal(board, move)), reset: Game.Truth(Chess.resets(board, move))) ->
  M.Lt(M.position(Address.position(Graph.address(Graph.route(anchor, board, move)))), M.position(board)):
  %Equal.sym(P.Position, Address.position(Graph.address(Graph.route(anchor, board, move))), Chess.after(board, move),
    GraphProof.route_position(anchor, board, move)) : M.Lt(M.position(_), M.position(board))
  Selection.legal_reset(board, move, legal, reset)

def earlier_directory(~C: Nat -> Data,
  ~build: @+stage: Nat -> @+width: Nat -> C(width) -> List<&2, Stages.Stage> -> List<&2, Registry.Named>,
  +count: Nat, +width: Nat, +context: C(width), +target: P.Position, +current: Nat,
  earlier: M.Lt(M.position(target), current), bounded: M.Le(current, 1n+count)) ->
  &directory: List<&2, Registry.Named> ->
    {Stages.find(Stages.schedule(~C, ~build, count, width, context), M.position(target)) == Some{directory} : Maybe<&2, List<&2, Registry.Named>>}:
  match target:
    case P.Position{turn, wk, bk, pieces, ep, square}:
      schedule_found(~C, ~build, count, 1n+M.men(pieces), width, context,
        MeasureProof.trans(1n+M.position(target), current, 1n+count, earlier, bounded))

# No assumed successful stage lookup: a legal reset and the completed bound
# suffice. This does not assume that build supplies every material directory.
def reset_directory(~C: Nat -> Data,
  ~build: @+stage: Nat -> @+width: Nat -> C(width) -> List<&2, Stages.Stage> -> List<&2, Registry.Named>,
  +count: Nat, +width: Nat, +context: C(width), +anchor: Game.Player, +board: P.Position, +move: Chess.Action,
  legal: Game.Truth(Chess.legal(board, move)), reset: Game.Truth(Chess.resets(board, move)), bounded: M.Le(M.position(board), 1n+count)) ->
  &directory: List<&2, Registry.Named> ->
    {Stages.find(Stages.schedule(~C, ~build, count, width, context), M.position(Address.position(Graph.address(Graph.route(anchor, board, move))))) ==
      Some{directory} : Maybe<&2, List<&2, Registry.Named>>}:
  earlier_directory(~C, ~build, count, width, context, Address.position(Graph.address(Graph.route(anchor, board, move))), M.position(board),
    routed_stage(anchor, board, move, legal, reset), bounded)
