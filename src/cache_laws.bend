import Base
import ./game.bend as Game
import ./finite_table.bend as Finite
import ./pawn_tables.bend as PawnTables
import ./position.bend as Position
import ./position_index.bend as PositionIndex
import ./chess.bend as CommonChess
import ./clock_solver.bend as ClockSolver
import ./position_address.bend as PositionAddress
import ./chess_graph.bend as ChessGraph
import ./dependency_engine.bend as Dependencies
import ./table_cache.bend as TableCache
import ./material_cache.bend as MaterialCache
import ./component_cache.bend as Components
import ./chess_measure.bend as Measure
import ./chess_component.bend as ChessComponent
import ./chess_cache.bend as ChessCache
import ./material_directory.bend as MaterialDirectory
import ./chess_solver.bend as ChessSolver
import ./chess_solver_proof.bend as ChessSolverProof
import ./chess_cache_invariant.bend as CacheInvariant
import ./chess_game.bend as ChessGame

# Supporting laws for cache/index machinery and the clock-layer alternative.
# Exact-width reads neither pad nor truncate keys. Signatures include ordered
# piece kinds and relative owners. Missing dependencies remain explicit None.
# Stages derive from destination measure, not offsets in a cache list.
#
# Distinguish coverage from semantics: directory/schedule completeness does not
# make arbitrary callback values correct WDL. StageRule and successful execution
# are explicit premises of the cached generator's semantic invariant theorem.
# StageRule is tied to a fixed clock limit. Those premises are not discharged
# for the general cached chess_solver by these laws. The direct chess_tables
# generator's unconditional public theorem is independent of that obligation.
# Off-stage entries are padding, not assertions of drawn chess positions.
# A clock component theorem certifies its supplied graph, not that graph's
# correspondence to chess or the correctness of externally supplied resets.
# Every law here is discharged by ../PROOF.bend.

# These semantic bridges remove dependence on unfolding fuel before proving
# cached layers equal the chess game. They do not assume cache correctness.
law common_chess_unfolding_is_fuel_independent:
  for +left: Nat
  for +right: Nat
  for +items: List<&2, ChessGame.State>
  for +limit: Nat
  for +actions: Nat
  for first: ChessGame.NoCutoff(left, items, limit, actions)
  for second: ChessGame.NoCutoff(right, items, limit, actions)
  {ChessGame.forest(left, items, limit, actions) == ChessGame.forest(right, items, limit, actions) : List<&2, Game.Tree>}

law common_chess_continuations_are_standalone_games:
  for +limit: Nat
  for +clock: Nat
  for +board: Position.Position
  {ChessGame.tree(limit, 1n+clock, board) ==
   ChessGame.assemble(ChessGraph.node(14n, Game.White{}, board),
     ChessGame.standalone(ChessGame.states(limit, 1n+clock,
       ChessGame.children(ChessGraph.node(14n, Game.White{}, board))), limit)) : Game.Tree}

law common_chess_zero_clock_preserves_terminal_precedence:
  for +limit: Nat
  for +board: Position.Position
  {ChessGame.tree(limit, 0n, board) == Game.End{CommonChess.boundary(CommonChess.view(14n, board))} : Game.Tree}

law common_correct_cache_extends:
  for ~expected: Position.Position -> Game.Outcome
  for +count: Nat
  for +capacity: Nat
  for +entries: List<&2, MaterialCache.Named>
  for +previous: List<&2, Components.Stage>
  for old: CacheInvariant.Correct(~expected, count, capacity, previous)
  for current: CacheInvariant.Stratum(~expected, 1n+count, capacity, entries)
  CacheInvariant.Correct(~expected, 1n+count, capacity, Components.Stage{1n+count, entries} <> previous)

law common_invariant_supplies_correct_resets:
  for ~expected: Position.Position -> Game.Outcome
  for +width: Nat
  for +count: Nat
  for +capacity: Nat
  for +stages: List<&2, Components.Stage>
  for +anchor: Game.Player
  for +board: Position.Position
  for +move: CommonChess.Action
  for correct: CacheInvariant.Correct(~expected, count, capacity, stages)
  for legal: Game.Truth(CommonChess.legal(board, move))
  for resets: Game.Truth(CommonChess.resets(board, move))
  for bounded: Measure.Le(Measure.position(board), 1n+count)
  for material: Measure.Le(List.length(&2, Position.Descriptor, ChessComponent.material(anchor, board)), capacity)
  {ChessCache.reset(width, stages, ChessGraph.address(ChessGraph.route(anchor, board, move))) ==
    Some{ClockSolver.Reset{expected(PositionAddress.position(ChessGraph.address(ChessGraph.route(anchor, board, move))))}} : Maybe<&2, ClockSolver.Edge<width>>}

law common_generated_cache_invariant:
  for ~expected: Position.Position -> Game.Outcome
  for ~limit: Nat
  for ~sound: CacheInvariant.StageRule(~expected, limit)
  for +count: Nat
  for +capacity: Nat
  for +result: List<&2, Components.Stage>
  for success: {ChessSolver.generate(count, capacity, limit) == Some{result} : Maybe<&2, List<&2, Components.Stage>>}
  CacheInvariant.Correct(~expected, count, capacity, result)

law common_scheduled_chess_nodes_compile:
  for ~C: Data
  for ~solve: @+name: List<&2, Position.Descriptor> -> Nat -> C -> List<&2, Components.Stage> -> Finite.Table(MaterialDirectory.width(name), Game.Outcome)
  for +actions: Nat
  for +count: Nat
  for +capacity: Nat
  for +context: C
  for +anchor: Game.Player
  for +board: Position.Position
  for bounded: Measure.Le(Measure.position(board), 1n+count)
  for material: Measure.Le(List.length(&2, Position.Descriptor, ChessComponent.material(anchor, board)), capacity)
  exs node: ClockSolver.Node<ChessComponent.address_width(PositionAddress.of_position(anchor, board))>
  {ChessSolver.node(ChessComponent.address_width(PositionAddress.of_position(anchor, board)),
    MaterialDirectory.schedule(~C, ~solve, count, capacity, context), ChessGraph.node(actions, anchor, board)) == Some{node} :
    Maybe<&2, ClockSolver.Node<ChessComponent.address_width(PositionAddress.of_position(anchor, board))>>}

law common_compiler_preserves_node_backup:
  for +width: Nat
  for +stages: List<&2, Components.Stage>
  for +node: ChessGraph.Node
  for +previous: Finite.Table(width, Game.Outcome)
  {ChessSolverProof.node_value(width, ChessSolver.node(width, stages, node), previous) ==
    ChessSolverProof.backup(width, stages, node, previous) : Maybe<&2, Game.Outcome>}

law common_compiled_graph_has_exact_entries:
  for +name: List<&2, Position.Descriptor>
  for +stage: Nat
  for +stages: List<&2, Components.Stage>
  for +graph: Finite.Table(MaterialDirectory.width(name), ClockSolver.Node<MaterialDirectory.width(name)>)
  for +key: Word(MaterialDirectory.width(name))
  for compiled: {ChessSolver.graph(name, stage, stages) == Some{graph} : Maybe<&2, Finite.Table(MaterialDirectory.width(name), ClockSolver.Node<MaterialDirectory.width(name)>)>}
  {ChessSolver.entry(name, stage, stages, key) == Some{Finite.get(MaterialDirectory.width(name), ClockSolver.Node<MaterialDirectory.width(name)>, key, graph)} : Maybe<&2, ClockSolver.Node<MaterialDirectory.width(name)>>}

law common_compiled_layer_preserves_entry_backup:
  for +name: List<&2, Position.Descriptor>
  for +stage: Nat
  for +stages: List<&2, Components.Stage>
  for +graph: Finite.Table(MaterialDirectory.width(name), ClockSolver.Node<MaterialDirectory.width(name)>)
  for +key: Word(MaterialDirectory.width(name))
  for +previous: Finite.Table(MaterialDirectory.width(name), Game.Outcome)
  for compiled: {ChessSolver.graph(name, stage, stages) == Some{graph} : Maybe<&2, Finite.Table(MaterialDirectory.width(name), ClockSolver.Node<MaterialDirectory.width(name)>)>}
  {Some{Finite.get(MaterialDirectory.width(name), Game.Outcome, key, ClockSolver.layer(MaterialDirectory.width(name), graph, ClockSolver.Next{previous}))} ==
    ChessSolverProof.node_value(MaterialDirectory.width(name), ChessSolver.entry(name, stage, stages, key), previous) : Maybe<&2, Game.Outcome>}

law common_component_solves_compiled_game:
  for +name: List<&2, Position.Descriptor>
  for +stage: Nat
  for +limit: Nat
  for +stages: List<&2, Components.Stage>
  for +graph: Finite.Table(MaterialDirectory.width(name), ClockSolver.Node<MaterialDirectory.width(name)>)
  for +key: Word(MaterialDirectory.width(name))
  for compiled: {ChessSolver.graph(name, stage, stages) == Some{graph} : Maybe<&2, Finite.Table(MaterialDirectory.width(name), ClockSolver.Node<MaterialDirectory.width(name)>)>}
  {ChessSolverProof.table_value(MaterialDirectory.width(name), ChessSolver.component(name, stage, limit, stages), key) ==
    Some{Game.evaluate(ClockSolver.tree(limit, MaterialDirectory.width(name), graph, key))} : Maybe<&2, Game.Outcome>}

law common_material_directory_is_complete:
  for ~C: Data
  for ~solve: @+name: List<&2, Position.Descriptor> -> C -> Finite.Table(MaterialDirectory.width(name), Game.Outcome)
  for +capacity: Nat
  for +name: List<&2, Position.Descriptor>
  for +context: C
  for bounded: Measure.Le(List.length(&2, Position.Descriptor, name), capacity)
  {MaterialCache.find(MaterialDirectory.build(~C, ~solve, capacity, context), name) ==
    Some{MaterialDirectory.entry(~C, ~solve, name, context)} : Maybe<&2, TableCache.Entry>}

law common_material_schedule_is_complete:
  for ~C: Data
  for ~solve: @+name: List<&2, Position.Descriptor> -> Nat -> C -> List<&2, Components.Stage> -> Finite.Table(MaterialDirectory.width(name), Game.Outcome)
  for +count: Nat
  for +query: Nat
  for +capacity: Nat
  for +context: C
  for +name: List<&2, Position.Descriptor>
  for bounded: Measure.Le(1n+query, count)
  for material: Measure.Le(List.length(&2, Position.Descriptor, name), capacity)
  MaterialDirectory.Available(MaterialDirectory.schedule(~C, ~solve, count, capacity, context), 1n+query, name)

law common_scheduled_resets_always_resolve:
  for ~C: Data
  for ~solve: @+name: List<&2, Position.Descriptor> -> Nat -> C -> List<&2, Components.Stage> -> Finite.Table(MaterialDirectory.width(name), Game.Outcome)
  for +count: Nat
  for +capacity: Nat
  for +context: C
  for +anchor: Game.Player
  for +board: Position.Position
  for +move: CommonChess.Action
  for legal: Game.Truth(CommonChess.legal(board, move))
  for reset: Game.Truth(CommonChess.resets(board, move))
  for bounded: Measure.Le(Measure.position(board), 1n+count)
  for material: Measure.Le(List.length(&2, Position.Descriptor, ChessComponent.material(anchor, board)), capacity)
  exs value: Game.Outcome
  {ChessCache.resolve(MaterialDirectory.schedule(~C, ~solve, count, capacity, context), ChessGraph.address(ChessGraph.route(anchor, board, move))) ==
    Some{value} : Maybe<&2, Game.Outcome>}

law common_reset_stage_is_scheduled:
  for ~C: Nat -> Data
  for ~build: @+stage: Nat -> @+width: Nat -> C(width) -> List<&2, Components.Stage> -> List<&2, MaterialCache.Named>
  for +count: Nat
  for +width: Nat
  for +context: C(width)
  for +anchor: Game.Player
  for +board: Position.Position
  for +move: CommonChess.Action
  for legal: Game.Truth(CommonChess.legal(board, move))
  for reset: Game.Truth(CommonChess.resets(board, move))
  for bounded: Measure.Le(Measure.position(board), 1n+count)
  exs directory: List<&2, MaterialCache.Named>
  {Components.find(Components.schedule(~C, ~build, count, width, context),
    Measure.position(PositionAddress.position(ChessGraph.address(ChessGraph.route(anchor, board, move))))) ==
    Some{directory} : Maybe<&2, List<&2, MaterialCache.Named>>}

law common_registered_reset_reads_exact_value:
  for +width: Nat
  for +stages: List<&2, Components.Stage>
  for +n: Nat
  for +material: Position.Material(n)
  for +key: Word(PositionIndex.width(n))
  for +directory: List<&2, MaterialCache.Named>
  for +table: Finite.Table(PositionIndex.width(n), Game.Outcome)
  for stage: {Components.find(stages, Measure.position(PositionAddress.position(PositionAddress.Address{n, material, key}))) == Some{directory} : Maybe<&2, List<&2, MaterialCache.Named>>}
  for entry: {MaterialCache.find(directory, MaterialCache.signature(n, material)) == Some{TableCache.Entry{PositionIndex.width(n), table}} : Maybe<&2, TableCache.Entry>}
  {ChessCache.reset(width, stages, PositionAddress.Address{n, material, key}) ==
    Some{ClockSolver.Reset{Finite.get(PositionIndex.width(n), Game.Outcome, key, table)}} : Maybe<&2, ClockSolver.Edge<width>>}

law common_empty_reset_cache_is_failure:
  for +width: Nat
  for +address: PositionAddress.Address
  {ChessCache.reset(width, Nil{}, address) == None{} : Maybe<&2, ClockSolver.Edge<width>>}

law common_missing_reset_is_failure:
  for +width: Nat
  for +stages: List<&2, Components.Stage>
  for +address: PositionAddress.Address
  for missing: {ChessCache.resolve(stages, address) == None{} : Maybe<&2, Game.Outcome>}
  {ChessCache.reset(width, stages, address) == None{} : Maybe<&2, ClockSolver.Edge<width>>}

law component_stage_matching_is_exact:
  for +left: Nat
  for +right: Nat
  for matches: Game.Truth(Components.equal(left, right))
  {left == right : Nat}

law completed_component_resolves_common_address:
  for +index: Nat
  for +n: Nat
  for +material: Position.Material(n)
  for +key: Word(PositionIndex.width(n))
  for +table: Finite.Table(PositionIndex.width(n), Game.Outcome)
  for +tail: List<&2, Components.Stage>
  {Components.resolve(
     Components.Stage{index, [MaterialCache.Named{MaterialCache.signature(n, material), TableCache.Entry{PositionIndex.width(n), table}}]} <> tail,
     index, PositionAddress.Address{n, material, key}) ==
   Some{Finite.get(PositionIndex.width(n), Game.Outcome, key, table)} : Maybe<&2, Game.Outcome>}

law next_stage_does_not_shadow_previous_component:
  for +index: Nat
  for +entries: List<&2, MaterialCache.Named>
  for +tail: List<&2, Components.Stage>
  for +name: List<&2, Position.Descriptor>
  {Components.select(Components.Stage{1n+index, entries} <> tail, index, name) ==
   Components.select(tail, index, name) : Maybe<&2, TableCache.Entry>}

law pawn_schedule_contains_only_completed_stages:
  for +count: Nat
  for +width: Nat
  for +limit: Nat
  for +promotions: List<&2, MaterialCache.Named>
  Components.Before(PawnTables.history(count, width, limit, promotions), 1n+count)

law completed_stage_cache_has_no_current_stage:
  for +stages: List<&2, Components.Stage>
  for +current: Nat
  for earlier: Components.Before(stages, current)
  {Components.find(stages, current) == None{} : Maybe<&2, List<&2, MaterialCache.Named>>}

law material_signature_matching_is_exact:
  for +left: List<&2, Position.Descriptor>
  for +right: List<&2, Position.Descriptor>
  for matches: Game.Truth(MaterialCache.equal(left, right))
  {left == right : List<&2, Position.Descriptor>}

law material_cache_hit_has_matching_signature:
  for +entries: List<&2, MaterialCache.Named>
  for +query: List<&2, Position.Descriptor>
  for +entry: TableCache.Entry
  for found: {MaterialCache.find(entries, query) == Some{entry} : Maybe<&2, TableCache.Entry>}
  MaterialCache.Hit(entries, query, entry)

law material_cache_resolves_common_address:
  for +n: Nat
  for +material: Position.Material(n)
  for +key: Word(PositionIndex.width(n))
  for +table: Finite.Table(PositionIndex.width(n), Game.Outcome)
  for +tail: List<&2, MaterialCache.Named>
  {MaterialCache.resolve(
     MaterialCache.Named{MaterialCache.signature(n, material), TableCache.Entry{PositionIndex.width(n), table}} <> tail,
     PositionAddress.Address{n, material, key}) ==
   Some{Finite.get(PositionIndex.width(n), Game.Outcome, key, table)} : Maybe<&2, Game.Outcome>}

law material_cache_miss_is_explicit:
  for +query: List<&2, Position.Descriptor>
  for +width: Nat
  for +key: Word(width)
  {MaterialCache.lookup(Nil{}, query, width, key) == None{} : Maybe<&2, Game.Outcome>}

law completed_dependency_lookup_is_exact:
  for +width: Nat
  for +key: Word(width)
  for +table: Finite.Table(width, Game.Outcome)
  {TableCache.lookup(width, key, TableCache.Entry{width, table}) ==
   Some{Finite.get(width, Game.Outcome, key, table)} : Maybe<&2, Game.Outcome>}

law successful_dependency_lookup_has_matching_width:
  for +stored_width: Nat
  for +query_width: Nat
  for +key: Word(query_width)
  for +table: Finite.Table(stored_width, Game.Outcome)
  for +result: Game.Outcome
  for found: {TableCache.lookup(query_width, key, TableCache.Entry{stored_width, table}) == Some{result} : Maybe<&2, Game.Outcome>}
  {stored_width == query_width : Nat}

law dependency_cache_returns_completed_value:
  for -A: Data
  for +value: A
  for +cache: List<&2, A>
  {Dependencies.lookup(0n, A, value <> cache) == Some{value} : Maybe<&2, A>}

law dependency_cache_preserves_earlier_values:
  for -A: Data
  for +offset: Nat
  for +value: A
  for +cache: List<&2, A>
  {Dependencies.lookup(1n+offset, A, value <> cache) == Dependencies.lookup(offset, A, cache) : Maybe<&2, A>}

law missing_dependency_is_explicit:
  for -A: Data
  for offset: Nat
  {Dependencies.lookup(offset, A, Nil{}) == None{} : Maybe<&2, A>}

law common_clock_component_wdl_is_correct:
  for +remaining: Nat
  for +width: Nat
  for +graph: Finite.Table(width, ClockSolver.Node<width>)
  for +key: Word(width)
  Game.CorrectByte(ClockSolver.tree(remaining, width, graph, key),
    Finite.read(ClockSolver.file(remaining, width, graph), Finite.offset(width, key)))

law common_clock_component_file_has_exact_length:
  for +remaining: Nat
  for +width: Nat
  for +graph: Finite.Table(width, ClockSolver.Node<width>)
  {List.length(&2, U32, ClockSolver.file(remaining, width, graph)) == Finite.size(width) : Nat}
