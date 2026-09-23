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
import ./src/four_tables_proof.bend as FourProof

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

def Laws.four_wdl_is_fully_correct(limit, horizon, moves, actions, width, format, material, board, valid):
  +game = Four.tree(limit, moves, FourIndex.position(material, board))
  (Game.evaluate(game),
    (FourProof.serialized_value(width, format, limit, moves, material, board),
     +player =>
       (yes => GameProof.sound(game, player, yes),
        strategy => GameProof.complete(game, player, strategy))))

def Laws.four_file_has_exact_length(width, limit, moves, material):
  FourProof.file_length(width, limit, moves, material)
