import Base
import ./src/game.bend as Game
import ./src/pawnless_chess.bend as Chess
import ./src/pawnless_index.bend as Index
import ./src/finite_table.bend as Finite
import ./src/pawnless_tables.bend as Tables

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
