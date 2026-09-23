import Base
import ./LAWS.bend as Laws
import ./src/game.bend as Game
import ./src/game_proof.bend as GameProof
import ./src/pawnless_chess.bend as Chess
import ./src/pawnless_index_proof.bend as IndexProof
import ./src/pawnless_moves_proof.bend as MovesProof
import ./src/pawnless_tables_proof.bend as TablesProof

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
