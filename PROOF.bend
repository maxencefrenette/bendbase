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
