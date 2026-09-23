import Base
import ./src/game.bend as Game
import ./src/pawnless_chess.bend as Chess
import ./src/pawnless_index.bend as Index
import ./src/finite_table.bend as Finite
import ./src/pawnless_tables.bend as Tables
import ./src/pawn_chess.bend as Pawn
import ./src/pawn_tables.bend as PawnTables
import ./src/material_chess.bend as Material

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
# existing KPK rules; four-man pawn rules and all four-man WDL solving are NOT
# certified here. Existing three-man solvers have not been switched over.
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
