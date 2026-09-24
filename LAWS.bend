import Base
import ./src/game.bend as Game
import ./src/pawnless_chess.bend as Chess
import ./src/pawnless_index.bend as Index
import ./src/finite_table.bend as Finite
import ./src/pawnless_tables.bend as Tables
import ./src/pawn_chess.bend as Pawn
import ./src/pawn_tables.bend as PawnTables
import ./src/material_chess.bend as Material
import ./src/four_chess.bend as Four
import ./src/four_index.bend as FourIndex
import ./src/one_pawn_chess.bend as OnePawn
import ./src/one_pawn_game.bend as OnePawnGame
import ./src/one_pawn_tables.bend as OnePawnTables
import ./src/two_pawn_chess.bend as TwoPawn
import ./src/two_pawn_game.bend as TwoPawnGame
import ./src/two_pawn_tables.bend as TwoPawnTables
import ./src/pawnless_generator.bend as PawnlessGenerator
import ./src/position.bend as Position
import ./src/position_index.bend as PositionIndex
import ./src/position_legacy.bend as PositionLegacy
import ./src/chess.bend as CommonChess
import ./src/clock_solver.bend as ClockSolver
import ./src/position_address.bend as PositionAddress
import ./src/chess_graph.bend as ChessGraph
import ./src/dependency_engine.bend as Dependencies
import ./src/table_cache.bend as TableCache
import ./src/material_cache.bend as MaterialCache
import ./src/component_cache.bend as Components
import ./src/chess_measure.bend as Measure
import ./src/chess_component.bend as ChessComponent
import ./src/chess_cache.bend as ChessCache
import ./src/material_directory.bend as MaterialDirectory
import ./src/chess_solver.bend as ChessSolver
import ./src/chess_solver_proof.bend as ChessSolverProof
import ./src/chess_compile_total.bend as CompileTotal
import ./src/chess_cache_invariant.bend as CacheInvariant
import ./src/chess_game.bend as CommonGame
import ./src/chess_tables.bend as CommonTables

# Unconditional correctness-first N-men generator. It tabulates the common
# chess game directly; no assumed StageRule, successful compilation, or cache
# values appear in these laws. Material and position keys remain symbolic.
# The game has no castling, includes EP and every promotion, uses the automatic
# 100-halfmove draw convention, and gives existing terminals precedence.
# NoCutoff proves that the natural-number recursion bound never invents a draw.
# This is NOT the cached clock-layer implementation's missing equivalence proof.
# The direct generator sacrifices speed completely; no generation benchmark or
# practical feasibility claim is made. Existing optimized file mains are not
# migrated. The common file writer stores the full internal index, including
# EP states, in one byte per key (1/0/255), separately for each signature.
law common_chess_game_never_truncates:
  for +limit: Nat
  for +remaining: Nat
  for +actions: Nat
  for +board: Position.Position
  CommonGame.NoCutoff(Measure.budget(limit, Measure.position(board), remaining),
    [CommonGame.State{remaining, board}], limit, actions)

law common_generated_wdl_is_fully_correct:
  for +name: List<&2, Position.Descriptor>
  for +key: Word(MaterialDirectory.width(name))
  CommonGame.NoCutoff(Measure.budget(100n, Measure.position(CommonTables.position(name, key)), 100n),
    [CommonGame.State{100n, CommonTables.position(name, key)}], 100n, 14n) &
  Game.CorrectByte(CommonGame.tree(100n, 100n, CommonTables.position(name, key)),
    Finite.read(CommonTables.file(name, 100n), Finite.offset(MaterialDirectory.width(name), key)))

law common_generated_directory_reads_correct_values:
  for +capacity: Nat
  for +limit: Nat
  for +name: List<&2, Position.Descriptor>
  for +key: Word(MaterialDirectory.width(name))
  for bounded: Measure.Le(List.length(&2, Position.Descriptor, name), capacity)
  {MaterialCache.lookup(CommonTables.generate(capacity, limit), name, MaterialDirectory.width(name), key) ==
    Some{Game.evaluate(CommonGame.tree(limit, limit, CommonTables.position(name, key)))} : Maybe<&2, Game.Outcome>}

law common_generated_file_has_exact_length:
  for +name: List<&2, Position.Descriptor>
  for +limit: Nat
  {List.length(&2, U32, CommonTables.file(name, limit)) == Finite.size(MaterialDirectory.width(name)) : Nat}

law common_legal_lines_have_finite_bound:
  for +moves: List<&2, CommonChess.Action>
  for +limit: Nat
  for +remaining: Nat
  for +board: Position.Position
  for legal: CommonGame.Line(moves, limit, remaining, board)
  Measure.Le(List.length(&2, CommonChess.Action, moves), Measure.budget(limit, Measure.position(board), remaining))

# Semantic stage induction is now factored explicitly. These parametric laws
# do NOT assert that an arbitrary expected function is chess WDL. StageRule
# remains the component semantic obligation, and generated correctness is
# conditional on both that rule and successful execution of the real builder.
# No fallback outcome is introduced to bypass either obligation.
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

# Castling is permanently unavailable throughout the modeled game, not just
# at stored roots. En passant remains modeled in continuations.
# Material composition plus pawn progress orders reset dependencies; quiet
# moves use the remaining-clock induction within a component.
# Compilation below needs only source size and completed-stage bounds. It is
# proved for the total directory schedule, whose callback values are arbitrary.
# Establishing the actual fallible generator's schedule and semantic invariant
# is still required; this law does not assume or assert those values are WDL.
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

# The common executable compiler connects addressed chess nodes to the clock
# solver for arbitrary material signatures. Missing dependencies abort, never
# become draws. These are compiler/solver refinement laws, NOT yet a full
# N-men chess WDL theorem: successful compilation and the semantic invariant
# of earlier cache stages still need to be established for generate.
# Inactive-stage slots are padding; correctness only concerns live positions.
# All proofs below are structural, with position keys left symbolic.
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

# The common directory enumerates ordered material signatures, not positions:
# every non-king kind/relative owner, and every length up to capacity. The
# solver callback must return the signature's exact-width table. Completeness
# is independent of its values and does NOT assume that those values are WDL.
# The scheduled builder now guarantees BOTH stage and material coverage for
# reset edges. Only source-size and completed-stage bounds remain as premises.
# Semantic correctness of solve and production-generator integration remain.
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

# Reset resolution derives its stage from the destination, never a family
# offset. The scheduler really contains each earlier positive stage. The
# table-read theorem below also supports arbitrary externally supplied caches:
# it is conditional on registration of the exact material and width. The
# common builder above discharges coverage, but not semantic WDL correctness.
# None is NOT a draw.
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

# Quiet moves preserve the full ordered cache signature (owners AND kinds),
# not just the number of pieces. Their actual routed addresses therefore stay
# in the current material/measure component, with exactly the same key width.
# This establishes quiet-component closure; it does not yet establish material
# coverage or correctness of the earlier components needed by reset lookups.
law common_address_preserves_component:
  for +anchor: Game.Player
  for +board: Position.Position
  {ChessComponent.of_address(PositionAddress.of_position(anchor, board)) == ChessComponent.of_position(anchor, board) : ChessComponent.Key}

law common_legal_quiet_moves_preserve_material:
  for +anchor: Game.Player
  for +board: Position.Position
  for +move: CommonChess.Action
  for legal: Game.Truth(CommonChess.legal(board, move))
  for quiet: Game.Truth(Bool.not(CommonChess.resets(board, move)))
  {ChessComponent.material(anchor, CommonChess.after(board, move)) == ChessComponent.material(anchor, board) : List<&2, Position.Descriptor>}

law common_quiet_routes_stay_in_component:
  for +anchor: Game.Player
  for +board: Position.Position
  for +move: CommonChess.Action
  for legal: Game.Truth(CommonChess.legal(board, move))
  for quiet: Game.Truth(Bool.not(CommonChess.resets(board, move)))
  {ChessComponent.of_address(ChessGraph.address(ChessGraph.route(anchor, board, move))) == ChessComponent.of_position(anchor, board) : ChessComponent.Key}

law common_quiet_routes_preserve_key_width:
  for +anchor: Game.Player
  for +board: Position.Position
  for +move: CommonChess.Action
  for legal: Game.Truth(CommonChess.legal(board, move))
  for quiet: Game.Truth(Bool.not(CommonChess.resets(board, move)))
  {ChessComponent.address_width(ChessGraph.address(ChessGraph.route(anchor, board, move))) ==
    ChessComponent.address_width(PositionAddress.of_position(anchor, board)) : Nat}

# Common dependency measure: two kings + one per other man + the sum of
# ranks remaining to promotion for every pawn. Double pushes consume two;
# promotion removes the pawn-distance contribution but keeps the man.
# The move-update proof is structural over arbitrary material, including EP.
# Legal selection and distinct occupancy establish the pawn-progress premise:
# every touched man is the selected mover, with the correct owner and geometry.
# Legal resets strictly decrease the measure; quiet moves preserve it.
# Combining it with the remaining halfmove clock gives a natural-number bound
# decreasing on EVERY legal continuation, including routed address/clock updates.
# These ordering laws do NOT yet claim N-men WDL correctness: complete cache
# coverage, component compilation, and production integration remain obligations.
law common_pawn_geometry_decreases_distance:
  for +owner: Game.Player
  for +from: Word(6n)
  for +dest: Word(6n)
  for +board: Position.Position
  for allowed: Game.Truth(CommonChess.pawn_geometry(owner, from, dest, board))
  Measure.Lt(Measure.distance(owner, dest), Measure.distance(owner, from))

law common_move_update_respects_measure:
  for +pieces: List<&2, Position.Man>
  for +from: Word(6n)
  for +dest: Word(6n)
  for +choice: Chess.Material
  for +ep: Bool
  for +victim: Word(6n)
  for progress: Measure.Progress(pieces, from, dest)
  Measure.Bound(Measure.changes(pieces, from, dest, ep, victim),
    Measure.men(CommonChess.move_men(pieces, from, dest, choice, ep, victim)), Measure.men(pieces))

law common_legal_resets_decrease_measure:
  for +board: Position.Position
  for +move: CommonChess.Action
  for legal: Game.Truth(CommonChess.legal(board, move))
  for reset: Game.Truth(CommonChess.resets(board, move))
  Measure.Lt(Measure.position(CommonChess.after(board, move)), Measure.position(board))

law common_legal_quiet_moves_preserve_measure:
  for +board: Position.Position
  for +move: CommonChess.Action
  for legal: Game.Truth(CommonChess.legal(board, move))
  for quiet: Game.Truth(Bool.not(CommonChess.resets(board, move)))
  {Measure.position(CommonChess.after(board, move)) == Measure.position(board) : Nat}

law common_legal_continuations_decrease_budget:
  for +limit: Nat
  for +remaining: Nat
  for +board: Position.Position
  for +move: CommonChess.Action
  for legal: Game.Truth(CommonChess.legal(board, move))
  Measure.Lt(Measure.budget(limit, Measure.position(CommonChess.after(board, move)),
    Bool.pick(Nat, CommonChess.resets(board, move), limit, remaining)),
    Measure.budget(limit, Measure.position(board), 1n+remaining))

law common_routed_continuations_decrease_budget:
  for +limit: Nat
  for +remaining: Nat
  for +anchor: Game.Player
  for +board: Position.Position
  for +move: CommonChess.Action
  for legal: Game.Truth(CommonChess.legal(board, move))
  Measure.Lt(Measure.budget(limit, Measure.position(PositionAddress.position(ChessGraph.address(ChessGraph.route(anchor, board, move)))),
    ChessGraph.next_clock(limit, 1n+remaining, ChessGraph.route(anchor, board, move))),
    Measure.budget(limit, Measure.position(board), 1n+remaining))

# Component identity is (stage, material signature). The generic scheduler
# stamps completed directories with their stage and exposes only earlier
# stages to the next builder. KPK's actual generator uses it for pawn pushes
# and final rank selection; no cache-list offsets encode pawn progress.
# Scheduling and chess ordering are proved separately. Connecting full cache
# coverage and compiling the common graph remain obligations. Existing WDL
# laws are intact.
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

# Material lookup compares the entire ordered signature, including relative
# owners and pawn kinds, and retains missing dependencies as None. This reader
# is used for executable capture/promotion dependencies and also accepts common
# N-men addresses. It does not choose a pawn stratum: the scheduler must supply
# the appropriate completed directory. Nor does it prove its stored WDL values;
# existing generator laws below discharge that obligation for their tables.
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

# Completed dependencies carry their own index width. Captures, promotions
# and pawn advances all use this lookup in the executable generators. A key
# is neither truncated nor padded to fit another component. Component/material
# selection is still an adapter obligation, separate from these indexing laws.
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

# Shared dependency storage is not a chess-specific bundle or rank datatype.
# These cache laws and the generic family/history proofs cover arbitrary
# payloads, including packed tables with different widths. Existing adapters
# still choose their chess strata and justify their explicit draw fallbacks;
# this does NOT yet prove a universal chess dependency order.
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

# Uniform graph construction, before dependency resolution. Each successor
# carries its resulting material and lossless position key, including EP.
# These statements quantify over arbitrary lists, not just three/four men.
# They do not assume that a dependency cache is populated or correctly ordered.
law successor_addresses_are_lossless:
  for +anchor: Game.Player
  for +position: Position.Position
  {PositionAddress.position(PositionAddress.of_position(anchor, position)) == position : Position.Position}

law successor_addresses_cannot_alias_distinct_positions:
  for +left_anchor: Game.Player
  for +right_anchor: Game.Player
  for +left: Position.Position
  for +right: Position.Position
  for same: {PositionAddress.of_position(left_anchor, left) == PositionAddress.of_position(right_anchor, right) : PositionAddress.Address}
  {left == right : Position.Position}

law common_graph_routes_to_actual_successor:
  for +anchor: Game.Player
  for +position: Position.Position
  for +move: CommonChess.Action
  {PositionAddress.position(ChessGraph.address(ChessGraph.route(anchor, position, move))) ==
   CommonChess.after(position, move) : Position.Position}

law common_graph_preserves_clock_reset:
  for +anchor: Game.Player
  for +position: Position.Position
  for +move: CommonChess.Action
  {ChessGraph.resets(ChessGraph.route(anchor, position, move)) == CommonChess.resets(position, move) : Bool}

# Used only when taking a move from a live node with remaining > 0. Terminal
# detection, including the clock-zero draw, happens before edge traversal.
law common_graph_applies_clock_policy:
  for +limit: Nat
  for +remaining: Nat
  for +anchor: Game.Player
  for +position: Position.Position
  for +move: CommonChess.Action
  {ChessGraph.next_clock(limit, remaining, ChessGraph.route(anchor, position, move)) ==
   Bool.pick(Nat, CommonChess.resets(position, move), limit, Nat.sub(remaining, 1n)) : Nat}

law common_graph_preserves_all_moves_and_terminal_results:
  for +width: Nat
  for +anchor: Game.Player
  for +position: Position.Position
  {ChessGraph.view(ChessGraph.node(width, anchor, position)) == CommonChess.view(width, position) : CommonChess.View}

# Common move specification: arbitrary lists of Q/R/B/N/pawns, two kings,
# no castling. Pawns advance in their owner's direction; double pushes need
# the starting rank and two empty squares; promotion offers all four kinds.
# EP removes the pawn behind the target, expires on every other move, and
# includes post-capture king safety. Asserted rights require a valid double-
# push predecessor. These laws certify enumeration against those move rules,
# not yet equivalence with every legacy chess module or N-men WDL generation.
law common_legal_moves_are_complete:
  for +width: Nat
  for format: {width == 14n : Nat}
  for +position: Position.Position
  for +move: CommonChess.Action
  for legal: Game.Truth(CommonChess.legal(position, move))
  CommonChess.Member(CommonChess.after(position, move), CommonChess.successors(width, position))

law common_legal_moves_are_sound:
  for +width: Nat
  for +position: Position.Position
  for +next: Position.Position
  for member: CommonChess.Member(next, CommonChess.successors(width, position))
  CommonChess.LegalSuccessor(width, position, next)

law common_successors_preserve_validity:
  for +width: Nat
  for +position: Position.Position
  for +next: Position.Position
  for member: CommonChess.Member(next, CommonChess.successors(width, position))
  Game.Truth(CommonChess.valid(next))

# A component theorem, not a substitute for chess integration: terminal nodes
# must encode mate/stalemate/dead positions; quiet edges must index the same
# component; reset edges must contain proven outcomes of earlier dependencies
# at clock zero. The clock solver has no material-specific branches. The law
# below proves its serialized result against the supplied component game.
# Establishing the graph/dependency obligations for chess remains separate.
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

# N-men consolidation foundation. n counts non-king pieces. Material fixes
# ordered piece kinds (including pawns) and relative owners; boards carry
# squares, side to move and explicit EP continuation state. These laws cover
# representation and lossless conversion, NOT yet N-men legal moves or WDL.
# Existing generators/file formats and their chess correctness laws below
# remain authoritative until migration to the common solver is complete.
law general_position_index_roundtrip:
  for +n: Nat
  for +board: Position.Board(n)
  {PositionIndex.decode(n, PositionIndex.encode(n, board)) == board : Position.Board(n)}

law general_position_index_is_injective:
  for +n: Nat
  for +left: Position.Board(n)
  for +right: Position.Board(n)
  for same: {PositionIndex.encode(n, left) == PositionIndex.encode(n, right) : Word(PositionIndex.width(n))}
  {left == right : Position.Board(n)}

law general_material_has_exact_piece_count:
  for +n: Nat
  for +material: Position.Material(n)
  for +board: Position.Board(n)
  for +owner: Game.Player
  {List.length(&2, Position.Man, Position.men(n, material, board, owner)) == n : Nat}

law three_man_embedding_is_lossless:
  for +board: Chess.Board
  {PositionLegacy.to_three(PositionLegacy.from_three(board)) == board : Chess.Board}

law four_man_embedding_is_lossless:
  for +board: FourIndex.Board
  {PositionLegacy.to_four(PositionLegacy.from_four(board)) == board : FourIndex.Board}

law three_man_embedding_preserves_position:
  for +kind: Chess.Material
  for +board: Chess.Board
  {Position.position(1n, PositionLegacy.three_material(Position.Piece{kind}), PositionLegacy.from_three(board)) ==
   PositionLegacy.lift_pawnless(Material.from_three(kind, board)) : Position.Position}

law four_man_embedding_preserves_position:
  for +material: FourIndex.Material
  for +board: FourIndex.Board
  {Position.position(2n, PositionLegacy.four_material(material), PositionLegacy.from_four(board)) ==
   PositionLegacy.lift_pawnless(FourIndex.position(material, board)) : Position.Position}

law kpk_embedding_preserves_position:
  for +advance: Nat
  for +position: Pawn.Position
  {Position.position(1n, PositionLegacy.three_material(Position.Pawn{}), PositionLegacy.from_kpk(advance, position)) ==
   PositionLegacy.lift_kpk(advance, position) : Position.Position}

# Domain: two kings and one queen, rook, bishop, or knight, of either color;
# either side to move; no castling rights. Squares and moves are defined in
# pawnless_chess.bend. Its legal predicate enforces movement, obstruction,
# occupancy, and king safety. A legal capture leaves the drawn K-vs-K game.
#
# Terminal rules: checkmate wins for the other side; stalemate and insufficient
# material draw. Every continuing move consumes one halfmove. At zero remaining
# halfmoves, an already-delivered mate takes precedence; otherwise the game draws.
# Clock-zero queries begin with 100 halfmoves remaining, per the agreed convention.
# A capture is the only possible clock reset in this domain and immediately
# ends in K vs K, so 100 plies cover every continuing game. Repetition history
# and optional draw-claim mechanics are not modeled. The stored tables answer
# clock-zero queries, not queries at arbitrary nonzero halfmove clocks.
#
# Game.Forces describes strategies independently of the generator: choose a
# winning continuation on one's own turn, handle every reply on the other turn.

law legal_moves_are_complete:
  for +material: Chess.Material
  for +board: Chess.Board
  for +key: Word(7n)
  for legal: Game.Truth(Chess.legal(material, board, Chess.action(key)))
  Chess.Member(Chess.after(board, Chess.action(key)), Chess.successors(material, board))

law legal_moves_are_sound:
  for +material: Chess.Material
  for +board: Chess.Board
  for +next: Chess.State
  for member: Chess.Member(next, Chess.successors(material, board))
  Chess.LegalSuccessor(material, board, next)

law position_index_roundtrip:
  for +board: Chess.Board
  {Index.decode(Index.encode(board)) == board : Chess.Board}

# The equality-bound constants keep the checker reasoning symbolically. They
# are exactly the constants used by table_file.write; no board-dependent
# certificate, table scan, or unproved solver premise is required.
#
# CorrectByte gives BOTH directions, for BOTH players:
#   byte 1   iff White has a forcing strategy;
#   byte 255 iff Black has a forcing strategy (-1 as a signed byte);
#   byte 0   iff neither has one.
#
# This certifies the pure byte list passed by table_file.write to File.write_bytes.
# Execution trusts Bend's checker/compiler/runtime and the operating system's
# file IO; the theorem does not certify pre-existing files or generation speed.
law generated_wdl_is_fully_correct:
  for +remaining: Nat
  for horizon: {remaining == 100n : Nat}
  for +width: Nat
  for +format: {width == 20n : Nat}
  for +material: Chess.Material
  for +board: Chess.Board
  for valid: Game.Truth(Chess.valid(material, board))
  Game.CorrectByte(Chess.tree(remaining, material, board),
    Finite.read(Tables.file(remaining, width, material),
      Finite.offset(width, Index.encode_at(width, board))))

# One byte at every encoded slot. At width 20 the file has 2^20 bytes;
# invalid placements occupy slots but are outside the WDL correctness domain.
law generated_file_has_exact_length:
  for +remaining: Nat
  for +width: Nat
  for +material: Chess.Material
  {List.length(&2, U32, Tables.file(remaining, width, material)) == Finite.size(width) : Nat}

# KPK extends the domain to a single pawn of either color. Pawn ranks 1 and 8
# are invalid; promotion replaces the pawn with a queen, rook, bishop or knight.
# Single pushes need an empty destination. Double pushes are allowed only from
# the starting rank and need both squares empty. A pawn cannot capture in KPK:
# its only enemy piece is a king. En passant therefore cannot occur either.
# Legal king moves enforce occupancy and safety; capturing the pawn draws.
#
# Pawn.advance is ACTUAL distance to promotion, not a search-depth cutoff.
# King moves consume one halfmove. Every pawn move resets the clock to 100,
# including promotion; the promoted game uses the existing pawnless rules.
# Recursion decreases (distance, remaining clock), so even with resets it
# covers the entire game. The same terminal and draw conventions above apply.
law pawn_legal_moves_are_complete:
  for +advance: Nat
  for +position: Pawn.Position
  for +key: Word(7n)
  for legal: Game.Truth(Pawn.legal(advance, position, Pawn.action(key)))
  Pawn.Member(Pawn.after(advance, position, Pawn.action(key)), Pawn.successors(advance, position))

law pawn_legal_moves_are_sound:
  for +advance: Nat
  for +position: Pawn.Position
  for +next: Pawn.Edge
  for member: Pawn.Member(next, Pawn.successors(advance, position))
  Pawn.LegalSuccessor(advance, position, next)

# One file contains both pawn colors, using the same 20-bit board index and
# signed-byte WDL format. The theorem certifies the actual serialized byte list,
# not an auxiliary evaluator or a board-dependent certificate.
law generated_kpk_wdl_is_fully_correct:
  for +limit: Nat
  for horizon: {limit == 100n : Nat}
  for +width: Nat
  for +format: {width == 20n : Nat}
  for +board: Chess.Board
  for valid: Game.Truth(Pawn.valid_board(board))
  Game.CorrectByte(Pawn.tree(limit, board),
    Finite.read(PawnTables.file(limit, width),
      Finite.offset(width, Index.encode_at(width, board))))

law generated_kpk_file_has_exact_length:
  for +limit: Nat
  for +width: Nat
  {List.length(&2, U32, PawnTables.file(limit, width)) == Finite.size(width) : Nat}

# Foundation for four-man solving: two explicit kings plus an arbitrary list
# of colored Q/R/B/N pieces. All occupied squares obstruct sliders, friendly
# destinations and king captures are forbidden, and post-capture king safety
# is checked on the resulting board. No castling. Pawns continue to use the
# existing KPK rules; the one-pawn four-man extension is specified below. Existing
# three-man solvers have not been switched over.
#
# A move is a source/destination pair, independent of material count. Width
# 12 covers every pair. Keeping it equality-bound avoids expanding the finite
# key table while checking these structural proofs.
law material_moves_are_complete:
  for +width: Nat
  for format: {width == 12n : Nat}
  for +board: Material.Position
  for +move: Material.Action
  for legal: Game.Truth(Material.legal(board, move))
  Material.Member(Material.after(board, move), Material.successors(width, board))

law material_moves_are_sound:
  for +width: Nat
  for +board: Material.Position
  for +next: Material.Position
  for member: Material.Member(next, Material.successors(width, board))
  Material.LegalSuccessor(width, board, next)

law material_successors_are_valid:
  for +width: Nat
  for +board: Material.Position
  for +next: Material.Position
  for member: Material.Member(next, Material.successors(width, board))
  Game.Truth(Material.valid(next))

# Lossless representation bridge, not a claim that the old solvers already
# use the new rules or a proof of equivalence between both legality predicates.
law material_three_man_roundtrip:
  for +material: Chess.Material
  for +board: Chess.Board
  {Material.to_three(Material.from_three(material, board)) == Material.Single{material, board} : Material.Projection}

# These structural laws justify the material transitions in Four.forest:
# quiet moves cannot reset the clock by changing material; captures strictly
# reduce the number of non-kings. A four-man capture enters the three-man game
# with a fresh clock. A subsequent capture leaves bare kings and draws.
law material_moves_do_not_increase_count:
  for +capacity: Nat
  for +board: Material.Position
  for +move: Material.Action
  for bounded: Material.Bounded(capacity, board)
  Material.Bounded(capacity, Material.after(board, move))

law material_captures_reduce_count:
  for +capacity: Nat
  for +board: Material.Position
  for +move: Material.Action
  for bounded: Material.Bounded(1n+capacity, board)
  for captured: Game.Truth(Material.capture(board, move))
  Material.Bounded(capacity, Material.after(board, move))

law material_quiet_moves_preserve_count:
  for +board: Material.Position
  for +move: Material.Action
  for quiet: Game.Truth(Bool.not(Material.capture(board, move)))
  {Material.count(Material.after(board, move)) == Material.count(board) : Nat}

# Pawnless four-man domain: two kings plus ANY pair of Q/R/B/N, with either
# ownership relation and either color to move. Material and all squares remain
# universally quantified. No board scan is part of the proof.
#
# Rules follow the movement/check/mate rules of FIDE articles 3 and 5:
# https://handbook.fide.com/chapter/E012023
# As above, our agreed 100-halfmove terminal-draw convention replaces optional
# claims/repetition history; checkmate takes precedence at the clock boundary.
# Bare kings, a lone bishop/knight, and two same-square-color bishops are
# insufficient material. Two knights are NOT automatically insufficient.
# Four.single uses the SAME generalized move rules as Four.forest; it does not
# assume the unproved equivalence of the old and generalized move predicates.
#
# These laws certify the executable generator directly against Four's chess
# game tree and Game.Forces strategies. There is no intermediate reference solver.
# No proof claims Syzygy-level performance or that four-man files have been run.
# main.bend deliberately does NOT generate them; four_main.bend is opt-in.
# Width 26 gives one byte per board slot; move width 12 covers all source /
# destination pairs. The index includes both color reversals in each material
# configuration. The IO/runtime trust caveats for three-man files also apply.
law four_position_index_roundtrip:
  for +board: FourIndex.Board
  {FourIndex.decode(FourIndex.encode(board)) == board : FourIndex.Board}

# Executable pawnless four-man generator: clock-layer dynamic programming.
# Quiet continuations read the preceding layer. Captures read completed
# generalized three-man tables at clock zero, NOT a decremented four-man layer.
# Material shape is preserved by every move, so cache lookup cannot silently
# change either surviving piece's kind or ownership.
# The three-man dependencies are themselves computed and proved here using
# the generalized rules; no equivalence with the older three-man engine is assumed.
# This is executable but not benchmarked: Syzygy-level speed is still a goal,
# not an established property. No full four-man generation is run for the proof.
law generated_pawnless_four_wdl_is_fully_correct:
  for +limit: Nat
  for horizon: {limit == 100n : Nat}
  for +moves: Nat
  for actions: {moves == 12n : Nat}
  for +width: Nat
  for +format: {width == 26n : Nat}
  for +low: Nat
  for +low_format: {low == 20n : Nat}
  for +material: FourIndex.Material
  for +board: FourIndex.Board
  for valid: Game.Truth(Material.valid(FourIndex.position(material, board)))
  Game.CorrectByte(Four.tree(limit, moves, FourIndex.position(material, board)),
    Finite.read(PawnlessGenerator.file(limit, width, low, moves, material),
      Finite.offset(width, FourIndex.encode_at(width, board))))

law generated_pawnless_four_file_has_exact_length:
  for +limit: Nat
  for +width: Nat
  for +low: Nat
  for +moves: Nat
  for +material: FourIndex.Material
  {List.length(&2, U32, PawnlessGenerator.file(limit, width, low, moves, material)) == Finite.size(width) : Nat}

# Four-man one-pawn domain: two kings, exactly one pawn, and one Q/R/B/N.
# Both ownership relations and colors are included. The pawn's actual distance
# to promotion determines its rank; ranks 1/8 without promotion are invalid.
# Sliders see ALL blockers, including the pawn. Pawn attacks are diagonal,
# independently of blockers or pins. Every move checks post-move king safety.
# Pawn pushes require empty destinations; double pushes require the starting
# rank and both squares empty. Diagonal pawn moves require an enemy piece at
# the destination. Promotion (quiet or capturing) offers all four Q/R/B/N.
# No en passant is possible with only one pawn; no castling rights are modeled.
#
# Quiet king/piece moves consume a halfmove. Pawn moves and captures reset the
# clock to 100. Capturing the extra piece enters KPK; capturing the pawn enters
# pawnless three-man chess; promotion enters pawnless three/four-man chess.
# The well-founded recursion uses actual pawn distance, then clock: no search
# budget or assumed table certificate. Lower-material and pawnless games use
# the definitions already covered above. All terminal/draw conventions remain.
#
# The byte list uses Game.evaluate on the rules directly, without a duplicate
# solver. This certifies specification bytes, not generation speed or on-disk
# four-man files. The 26-bit layout stores the pawn as the first piece; the
# profile contains the non-pawn kind and whether its owner opposes the pawn.
# The action width is 8 for this domain and 12 for pawnless continuations.
law one_pawn_moves_are_complete:
  for +width: Nat
  for format: {width == 8n : Nat}
  for +advance: Nat
  for +board: OnePawn.Position
  for +move: OnePawn.Action
  for legal: Game.Truth(OnePawn.legal(advance, board, move))
  OnePawn.Member(OnePawn.after(advance, board, move), OnePawn.successors(width, advance, board))

law one_pawn_moves_are_sound:
  for +width: Nat
  for +advance: Nat
  for +board: OnePawn.Position
  for +next: OnePawn.Edge
  for member: OnePawn.Member(next, OnePawn.successors(width, advance, board))
  OnePawn.LegalSuccessor(width, advance, board, next)

law one_pawn_successors_are_safe:
  for +width: Nat
  for +advance: Nat
  for +board: OnePawn.Position
  for +next: OnePawn.Edge
  for member: OnePawn.Member(next, OnePawn.successors(width, advance, board))
  Game.Truth(OnePawn.safe(advance, next))

law one_pawn_four_wdl_is_fully_correct:
  for +limit: Nat
  for horizon: {limit == 100n : Nat}
  for +moves: Nat
  for actions: {moves == 8n : Nat}
  for +other_moves: Nat
  for other_actions: {other_moves == 12n : Nat}
  for +width: Nat
  for +format: {width == 26n : Nat}
  for +profile: OnePawnTables.Profile
  for +board: FourIndex.Board
  for valid: Game.Truth(OnePawn.valid(OnePawnTables.advance(board), OnePawnTables.position(profile, board)))
  Game.CorrectByte(OnePawnGame.tree(limit, moves, other_moves, OnePawnTables.advance(board), OnePawnTables.position(profile, board)),
    Finite.read(OnePawnTables.file(width, limit, moves, other_moves, profile),
      Finite.offset(width, FourIndex.encode_at(width, board))))

law one_pawn_four_file_has_exact_length:
  for +width: Nat
  for +limit: Nat
  for +moves: Nat
  for +other_moves: Nat
  for +profile: OnePawnTables.Profile
  {List.length(&2, U32, OnePawnTables.file(width, limit, moves, other_moves, profile)) == Finite.size(width) : Nat}

# Four-man two-pawn domain: KPPK and KPKP, either color and side to move.
# The two actual distances to promotion are structural recursion parameters,
# not search fuel. Quiet king moves consume one halfmove; pawn moves/captures
# reset the clock. Captures (including EP) enter KPK; promotion enters the
# one-pawn game and subsequently the already-defined pawnless game.
#
# Pawn movement, double pushes, captures, and all four promotions follow the
# rules above, with both pawns included in occupancy and attack calculations.
# An EP right identifies the immediately preceding double-pushed pawn; its
# starting/intermediate squares and predecessor king safety are validated.
# Only an opposing adjacent fifth-rank pawn may capture it, onto the empty
# intermediate square; the victim is removed and final king safety checked.
# Every non-double move expires the old right; a double push replaces it.
# Checkmate/stalemate include EP among legal replies, even at the clock boundary.
#
# To reuse the existing index, stored roots have NoEP (AND clock zero).
# This is an explicit domain restriction: clock zero does NOT imply NoEP.
# The game still includes all EP continuations after future double pushes.
# Probing roots with EP rights is not supported by this file format.
# Profile False is KPPK, True is KPKP; both pawn colors are in each 26-bit file.
# The byte-list definition uses Game.evaluate directly, whose strategy theorem
# is already proved for every finite game. No duplicate solver is necessary.
# No four-man table generation, position enumeration in the proof, performance
# claim, castling rights, or repetition history is added by this milestone.
law two_pawn_moves_are_complete:
  for +width: Nat
  for format: {width == 8n : Nat}
  for +a: Nat
  for +b: Nat
  for +board: TwoPawn.Position
  for +move: TwoPawn.Action
  for legal: Game.Truth(TwoPawn.legal(a, b, board, move))
  TwoPawn.Member(TwoPawn.after(a, b, board, move), TwoPawn.successors(width, a, b, board))

law two_pawn_moves_are_sound:
  for +width: Nat
  for +a: Nat
  for +b: Nat
  for +board: TwoPawn.Position
  for +next: TwoPawn.Edge
  for member: TwoPawn.Member(next, TwoPawn.successors(width, a, b, board))
  TwoPawn.LegalSuccessor(width, a, b, board, next)

law two_pawn_successors_are_safe:
  for +width: Nat
  for +a: Nat
  for +b: Nat
  for +board: TwoPawn.Position
  for +next: TwoPawn.Edge
  for member: TwoPawn.Member(next, TwoPawn.successors(width, a, b, board))
  Game.Truth(TwoPawn.safe(a, b, next))

law two_pawn_four_wdl_is_fully_correct:
  for +limit: Nat
  for horizon: {limit == 100n : Nat}
  for +moves: Nat
  for actions: {moves == 8n : Nat}
  for +other_moves: Nat
  for other_actions: {other_moves == 12n : Nat}
  for +width: Nat
  for +format: {width == 26n : Nat}
  for +profile: TwoPawnTables.Profile
  for +board: FourIndex.Board
  for valid: Game.Truth(TwoPawn.valid(TwoPawnTables.first_advance(board), TwoPawnTables.second_advance(profile, board), TwoPawnTables.position(profile, board)))
  Game.CorrectByte(TwoPawnGame.tree(limit, moves, other_moves, TwoPawnTables.first_advance(board), TwoPawnTables.second_advance(profile, board), TwoPawnTables.position(profile, board)),
    Finite.read(TwoPawnTables.file(width, limit, moves, other_moves, profile),
      Finite.offset(width, FourIndex.encode_at(width, board))))

law two_pawn_four_file_has_exact_length:
  for +width: Nat
  for +limit: Nat
  for +moves: Nat
  for +other_moves: Nat
  for +profile: TwoPawnTables.Profile
  {List.length(&2, U32, TwoPawnTables.file(width, limit, moves, other_moves, profile)) == Finite.size(width) : Nat}
