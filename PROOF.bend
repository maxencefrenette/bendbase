import Base
import ./LAWS.bend as Laws
import ./src/game.bend as Game
import ./src/game_proof.bend as GameProof
import ./src/pawnless_chess.bend as Chess
import ./src/pawnless_index_proof.bend as IndexProof
import ./src/pawnless_moves_proof.bend as MovesProof
import ./src/pawnless_tables_proof.bend as TablesProof
import ./src/pawn_chess.bend as Pawn
import ./src/pawn_moves_proof.bend as PawnMovesProof
import ./src/pawn_tables_proof.bend as PawnTablesProof
import ./src/material_moves_proof.bend as MaterialProof
import ./src/material_count_proof.bend as CountProof
import ./src/four_chess.bend as Four
import ./src/four_index.bend as FourIndex
import ./src/four_index_proof.bend as FourIndexProof
import ./src/one_pawn_game.bend as OnePawnGame
import ./src/one_pawn_tables.bend as OnePawnTables
import ./src/one_pawn_moves_proof.bend as OnePawnMovesProof
import ./src/one_pawn_tables_proof.bend as OnePawnProof
import ./src/two_pawn_game.bend as TwoPawnGame
import ./src/two_pawn_tables.bend as TwoPawnTables
import ./src/two_pawn_moves_proof.bend as TwoPawnMovesProof
import ./src/two_pawn_tables_proof.bend as TwoPawnProof
import ./src/pawnless_generator_proof.bend as GeneratorProof
import ./src/position_index_proof.bend as PositionIndexProof
import ./src/position_legacy_proof.bend as PositionLegacyProof
import ./src/chess_moves_proof.bend as CommonMovesProof
import ./src/clock_solver.bend as ClockSolver
import ./src/clock_solver_proof.bend as ClockSolverProof
import ./src/position_address_proof.bend as PositionAddressProof
import ./src/chess_graph_proof.bend as ChessGraphProof
import ./src/dependency_engine_proof.bend as DependencyProof
import ./src/table_cache_proof.bend as TableCacheProof
import ./src/material_cache_proof.bend as MaterialCacheProof
import ./src/component_cache_proof.bend as ComponentCacheProof
import ./src/pawn_tables.bend as PawnTables
import ./src/chess_measure_proof.bend as MeasureProof
import ./src/chess_selection_proof.bend as SelectionProof
import ./src/chess_component_proof.bend as ChessComponentProof
import ./src/chess_cache_proof.bend as ChessCacheProof
import ./src/chess_cache.bend as ChessCache
import ./src/material_directory_proof.bend as MaterialDirectoryProof
import ./src/chess_solver_proof.bend as ChessSolverProof
import ./src/chess_compile_total.bend as CompileTotal

def Laws.common_scheduled_chess_nodes_compile(C, solve, actions, count, capacity, context, anchor, board, bounded, material):
  CompileTotal.node(~C, ~solve, actions, count, capacity, context, anchor, board, bounded, material)

def Laws.common_compiler_preserves_node_backup(width, stages, node, previous):
  ChessSolverProof.node(width, stages, node, previous)

def Laws.common_compiled_graph_has_exact_entries(name, stage, stages, graph, key, compiled):
  ChessSolverProof.graph(name, stage, stages, graph, key, compiled)

def Laws.common_compiled_layer_preserves_entry_backup(name, stage, stages, graph, key, previous, compiled):
  ChessSolverProof.layer(name, stage, stages, graph, key, previous, compiled)

def Laws.common_component_solves_compiled_game(name, stage, limit, stages, graph, key, compiled):
  ChessSolverProof.component(name, stage, limit, stages, graph, key, compiled)

def Laws.common_material_directory_is_complete(C, solve, capacity, name, context, bounded):
  MaterialDirectoryProof.build(~C, ~solve, capacity, name, context, bounded)

def Laws.common_material_schedule_is_complete(C, solve, count, query, capacity, context, name, bounded, material):
  MaterialDirectoryProof.schedule(~C, ~solve, count, query, capacity, context, name, bounded, material)

def Laws.common_scheduled_resets_always_resolve(C, solve, count, capacity, context, anchor, board, move, legal, reset, bounded, material):
  MaterialDirectoryProof.reset_resolves(~C, ~solve, count, capacity, context, anchor, board, move, legal, reset, bounded, material)

def Laws.common_reset_stage_is_scheduled(C, build, count, width, context, anchor, board, move, legal, reset, bounded):
  ChessCacheProof.reset_directory(~C, ~build, count, width, context, anchor, board, move, legal, reset, bounded)

def Laws.common_registered_reset_reads_exact_value(width, stages, n, material, key, directory, table, stage, entry):
  ChessCacheProof.reset_registered(width, stages, n, material, key, directory, table, stage, entry)

def Laws.common_empty_reset_cache_is_failure(width, address):
  {==}

def Laws.common_missing_reset_is_failure(width, stages, address, missing):
  Equal.cong(Maybe<&2, Game.Outcome>, Maybe<&2, ClockSolver.Edge<width>>, value => ChessCache.reset_value(width, value),
    ChessCache.resolve(stages, address), None{}, missing)

def Laws.common_address_preserves_component(anchor, board):
  ChessComponentProof.address_component(anchor, board)

def Laws.common_legal_quiet_moves_preserve_material(anchor, board, move, legal, quiet):
  ChessComponentProof.legal_material(anchor, board, move, legal, quiet)

def Laws.common_quiet_routes_stay_in_component(anchor, board, move, legal, quiet):
  ChessComponentProof.routed_component(anchor, board, move, legal, quiet)

def Laws.common_quiet_routes_preserve_key_width(anchor, board, move, legal, quiet):
  ChessComponentProof.routed_width(anchor, board, move, legal, quiet)

def Laws.common_pawn_geometry_decreases_distance(owner, from, dest, board, allowed):
  MeasureProof.pawn_geometry(owner, from, dest, board, allowed)

def Laws.common_move_update_respects_measure(pieces, from, dest, choice, ep, victim, progress):
  MeasureProof.update(pieces, from, dest, choice, ep, victim, progress)

def Laws.common_legal_resets_decrease_measure(board, move, legal, reset):
  SelectionProof.legal_reset(board, move, legal, reset)

def Laws.common_legal_quiet_moves_preserve_measure(board, move, legal, quiet):
  SelectionProof.legal_quiet(board, move, legal, quiet)

def Laws.common_legal_continuations_decrease_budget(limit, remaining, board, move, legal):
  SelectionProof.legal_budget(limit, remaining, board, move, legal)

def Laws.common_routed_continuations_decrease_budget(limit, remaining, anchor, board, move, legal):
  ChessGraphProof.route_budget(limit, remaining, anchor, board, move, legal)

def Laws.component_stage_matching_is_exact(left, right, matches):
  ComponentCacheProof.equal_reflect(left, right, matches)

def Laws.completed_component_resolves_common_address(index, n, material, key, table, tail):
  ComponentCacheProof.resolve_head(index, n, material, key, table, tail)

def Laws.next_stage_does_not_shadow_previous_component(index, entries, tail, name):
  ComponentCacheProof.skip_next(index, entries, tail, name)

def Laws.pawn_schedule_contains_only_completed_stages(count, width, limit, promotions):
  ComponentCacheProof.schedule_before(~PawnTables.Schedule, ~PawnTables.component,
    count, width, PawnTables.ScheduleContext{limit, promotions})

def Laws.completed_stage_cache_has_no_current_stage(stages, current, earlier):
  ComponentCacheProof.current_missing(stages, current, earlier)

def Laws.material_signature_matching_is_exact(left, right, matches):
  MaterialCacheProof.reflect(left, right, matches)

def Laws.material_cache_hit_has_matching_signature(entries, query, entry, found):
  MaterialCacheProof.find_sound(entries, query, entry, found)

def Laws.material_cache_resolves_common_address(n, material, key, table, tail):
  MaterialCacheProof.resolve_head(n, material, key, table, tail)

def Laws.material_cache_miss_is_explicit(query, width, key):
  {==}

def Laws.completed_dependency_lookup_is_exact(width, key, table):
  TableCacheProof.exact(width, key, table)

def Laws.successful_dependency_lookup_has_matching_width(stored_width, query_width, key, table, result, found):
  TableCacheProof.width_matches(stored_width, query_width, key, table, result, found)

def Laws.dependency_cache_returns_completed_value(A, value, cache):
  DependencyProof.lookup_head(A, value, cache)

def Laws.dependency_cache_preserves_earlier_values(A, offset, value, cache):
  DependencyProof.lookup_previous(A, offset, value, cache)

def Laws.missing_dependency_is_explicit(A, offset):
  DependencyProof.lookup_missing(A, offset)

def Laws.successor_addresses_are_lossless(anchor, position):
  PositionAddressProof.roundtrip(anchor, position)

def Laws.successor_addresses_cannot_alias_distinct_positions(left_anchor, right_anchor, left, right, same):
  PositionAddressProof.injective(left_anchor, right_anchor, left, right, same)

def Laws.common_graph_routes_to_actual_successor(anchor, position, move):
  ChessGraphProof.route_position(anchor, position, move)

def Laws.common_graph_preserves_clock_reset(anchor, position, move):
  ChessGraphProof.route_reset(anchor, position, move)

def Laws.common_graph_applies_clock_policy(limit, remaining, anchor, position, move):
  ChessGraphProof.route_clock(limit, remaining, anchor, position, move)

def Laws.common_graph_preserves_all_moves_and_terminal_results(width, anchor, position):
  ChessGraphProof.node(width, anchor, position)

def Laws.common_legal_moves_are_complete(width, format, position, move, legal):
  CommonMovesProof.every_action(width, format, position, move, legal)

def Laws.common_legal_moves_are_sound(width, position, next, member):
  CommonMovesProof.present_legal(width, position, next, member)

def Laws.common_successors_preserve_validity(width, position, next, member):
  CommonMovesProof.successor_valid(width, position, next, member)

def Laws.common_clock_component_wdl_is_correct(remaining, width, graph, key):
  +game = ClockSolver.tree(remaining, width, graph, key)
  (Game.evaluate(game),
    (ClockSolverProof.serialized_value(remaining, width, graph, key),
     +player =>
       (yes => GameProof.sound(game, player, yes),
        strategy => GameProof.complete(game, player, strategy))))

def Laws.common_clock_component_file_has_exact_length(remaining, width, graph):
  ClockSolverProof.file_length(remaining, width, graph)

def Laws.general_position_index_roundtrip(n, board):
  PositionIndexProof.roundtrip(n, board)

def Laws.general_position_index_is_injective(n, left, right, same):
  PositionIndexProof.injective(n, left, right, same)

def Laws.general_material_has_exact_piece_count(n, material, board, owner):
  PositionIndexProof.men_count(n, material, board, owner)

def Laws.three_man_embedding_is_lossless(board):
  PositionLegacyProof.three_roundtrip(board)

def Laws.four_man_embedding_is_lossless(board):
  PositionLegacyProof.four_roundtrip(board)

def Laws.three_man_embedding_preserves_position(kind, board):
  PositionLegacyProof.three_position(kind, board)

def Laws.four_man_embedding_preserves_position(material, board):
  PositionLegacyProof.four_position(material, board)

def Laws.kpk_embedding_preserves_position(advance, position):
  PositionLegacyProof.kpk_position(advance, position)

def Laws.legal_moves_are_complete(material, board, key, legal):
  MovesProof.legal_present(material, board, key, legal)

def Laws.legal_moves_are_sound(material, board, next, member):
  MovesProof.present_legal(material, board, next, member)

def Laws.position_index_roundtrip(board):
  IndexProof.decode_encode(board)

def Laws.generated_wdl_is_fully_correct(remaining, horizon, width, format, material, board, valid):
  +game = Chess.tree(remaining, material, board)
  (Game.evaluate(game),
    (TablesProof.serialized_value(remaining, width, format, material, board),
     +player =>
       (yes => GameProof.sound(game, player, yes),
        strategy => GameProof.complete(game, player, strategy))))

def Laws.generated_file_has_exact_length(remaining, width, material):
  TablesProof.file_length(remaining, width, material)

def Laws.pawn_legal_moves_are_complete(advance, position, key, legal):
  PawnMovesProof.legal_present(advance, position, key, legal)

def Laws.pawn_legal_moves_are_sound(advance, position, next, member):
  PawnMovesProof.present_legal(advance, position, next, member)

def Laws.generated_kpk_wdl_is_fully_correct(limit, horizon, width, format, board, valid):
  +game = Pawn.tree(limit, board)
  (Game.evaluate(game),
    (PawnTablesProof.serialized_value(limit, width, format, board),
     +player =>
       (yes => GameProof.sound(game, player, yes),
        strategy => GameProof.complete(game, player, strategy))))

def Laws.generated_kpk_file_has_exact_length(limit, width):
  PawnTablesProof.file_length(limit, width)

def Laws.material_moves_are_complete(width, format, board, move, legal):
  MaterialProof.every_action(width, format, board, move, legal)

def Laws.material_moves_are_sound(width, board, next, member):
  MaterialProof.present_legal(width, board, next, member)

def Laws.material_successors_are_valid(width, board, next, member):
  MaterialProof.successor_valid(width, board, next, member)

def Laws.material_three_man_roundtrip(material, board):
  MaterialProof.three_roundtrip(material, board)

def Laws.material_moves_do_not_increase_count(capacity, board, move, bounded):
  CountProof.after_bounded(capacity, board, move, bounded)

def Laws.material_captures_reduce_count(capacity, board, move, bounded, captured):
  CountProof.after_captured(capacity, board, move, bounded, captured)

def Laws.material_quiet_moves_preserve_count(board, move, quiet):
  CountProof.after_quiet(board, move, quiet)

def Laws.four_position_index_roundtrip(board):
  FourIndexProof.roundtrip(board)

def Laws.one_pawn_moves_are_complete(width, format, advance, board, move, legal):
  OnePawnMovesProof.every_action(width, format, advance, board, move, legal)

def Laws.one_pawn_moves_are_sound(width, advance, board, next, member):
  OnePawnMovesProof.present_legal(width, advance, board, next, member)

def Laws.one_pawn_successors_are_safe(width, advance, board, next, member):
  OnePawnMovesProof.successor_safe(width, advance, board, next, member)

def Laws.one_pawn_four_wdl_is_fully_correct(limit, horizon, moves, actions, other_moves, other_actions, width, format, profile, board, valid):
  +game = OnePawnGame.tree(limit, moves, other_moves, OnePawnTables.advance(board), OnePawnTables.position(profile, board))
  (Game.evaluate(game),
    (OnePawnProof.serialized_value(width, format, limit, moves, other_moves, profile, board),
     +player =>
       (yes => GameProof.sound(game, player, yes),
        strategy => GameProof.complete(game, player, strategy))))

def Laws.one_pawn_four_file_has_exact_length(width, limit, moves, other_moves, profile):
  OnePawnProof.file_length(width, limit, moves, other_moves, profile)

def Laws.two_pawn_moves_are_complete(width, format, a, b, board, move, legal):
  TwoPawnMovesProof.every_action(width, format, a, b, board, move, legal)

def Laws.two_pawn_moves_are_sound(width, a, b, board, next, member):
  TwoPawnMovesProof.present_legal(width, a, b, board, next, member)

def Laws.two_pawn_successors_are_safe(width, a, b, board, next, member):
  TwoPawnMovesProof.successor_safe(width, a, b, board, next, member)

def Laws.two_pawn_four_wdl_is_fully_correct(limit, horizon, moves, actions, other_moves, other_actions, width, format, profile, board, valid):
  +game = TwoPawnGame.tree(limit, moves, other_moves, TwoPawnTables.first_advance(board), TwoPawnTables.second_advance(profile, board), TwoPawnTables.position(profile, board))
  (Game.evaluate(game),
    (TwoPawnProof.serialized_value(width, format, limit, moves, other_moves, profile, board),
     +player =>
       (yes => GameProof.sound(game, player, yes),
        strategy => GameProof.complete(game, player, strategy))))

def Laws.two_pawn_four_file_has_exact_length(width, limit, moves, other_moves, profile):
  TwoPawnProof.file_length(width, limit, moves, other_moves, profile)

def Laws.generated_pawnless_four_wdl_is_fully_correct(limit, horizon, moves, actions, width, format, low, low_format, material, board, valid):
  +game = Four.tree(limit, moves, FourIndex.position(material, board))
  (Game.evaluate(game),
    (GeneratorProof.serialized_value(limit, width, format, low, low_format, moves, material, board),
     +player =>
       (yes => GameProof.sound(game, player, yes),
        strategy => GameProof.complete(game, player, strategy))))

def Laws.generated_pawnless_four_file_has_exact_length(limit, width, low, moves, material):
  GeneratorProof.file_length(limit, width, low, moves, material)
