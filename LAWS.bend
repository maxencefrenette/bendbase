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
import ./src/chess.bend as CommonChess
import ./src/material_cache.bend as MaterialCache
import ./src/chess_measure.bend as Measure
import ./src/material_directory.bend as MaterialDirectory
import ./src/chess_game.bend as CommonGame
import ./src/chess_tables.bend as CommonTables

# Public chess and WDL contract. Run bend PROOF.bend to check this file AND
# every supporting law in src/chess_laws.bend, src/cache_laws.bend, and
# src/legacy_laws.bend. Moving a lemma does not remove it from that proof gate.
#
# Rules shared by the specifications:
# - WDL only, queried at halfmove clock zero; no DTZ/DTM.
# - Castling is unavailable at roots and throughout continuations.
# - Captures and pawn moves reset the allowance to 100 halfmoves. Other moves
#   consume one. At zero, an existing terminal result (including checkmate)
#   takes precedence; otherwise the game is drawn.
# - Stalemate and insufficient material draw. Two knights are not automatically
#   insufficient. Repetition history and optional draw claims are not modeled.
# - Pawn promotion includes Q/R/B/N; EP is included wherever the domain permits.
#
# CorrectByte states BOTH directions for BOTH players: 1 iff White can force
# a win, 255 (-1) iff Black can force a win, and 0 iff neither can force a win.
# Game.Forces describes strategies independently of the table generator.
# Theorems certify pure byte lists, not pre-existing files. File IO, Bend's
# checker/compiler/runtime, and the operating system are trusted boundaries.
# No theorem promises generation speed, compactness, or Syzygy compatibility.

# 1. Direct common generator: arbitrary ordered material, including pawns.
# chess_tables / chess_table_file tabulate the common game directly. Keys and
# material stay symbolic in the proof. NoCutoff rules out artificial search
# truncation. The internal files include EP states and one byte per full key.
# These unconditional laws do NOT certify the alternative cached chess_solver;
# its conditional integration lemmas are in src/cache_laws.bend.
# This direct generator is correctness-first, not a practical-speed solver.
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

# 2. Common move rules and safety.
# chess.bend defines movement, obstruction, occupancy, king safety, promotion,
# double pushes and EP. EP rights require a valid double-push predecessor and
# expire on other moves. Width 14 covers all source/destination/promotion
# encodings; completeness is against these explicitly modeled rules.
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

# 3. Existing specialized three-man file generators.
# Pawnless: KQK/KRK/KBK/KNK, either color and side to move. Captures leave KK.
# KPK: either pawn color; pushes reset the clock, promotions enter pawnless
# chess, and capturing the pawn draws. EP cannot occur with one pawn.
# Both use the existing 20-bit index and one signed-WDL byte per slot.
# Invalid placements are outside these specialized WDL theorems' valid domain.
# Equality-bound widths/horizons retain the exact constants used by the writer
# without expanding their finite domains during proof checking.
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

law generated_file_has_exact_length:
  for +remaining: Nat
  for +width: Nat
  for +material: Chess.Material
  {List.length(&2, U32, Tables.file(remaining, width, material)) == Finite.size(width) : Nat}

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

# 4. Existing four-man implementations and formats.
# Pawnless: every Q/R/B/N pair and ownership relation; executable clock layers,
# with captures reading proved three-man outcomes at clock zero.
# One-pawn: one pawn and one Q/R/B/N, all promotions and captures.
# Two-pawn: KPPK/KPKP, either color; EP is modeled in continuations.
# The pawnful byte lists directly evaluate their domain-specific game trees;
# these statements do not certify an optimized pawnful four-man generator.
# Existing four-man files use the 26-bit index, with NO EP rights at stored
# roots. This is an explicit restriction: clock zero does not imply no EP.
# Each table includes both color reversals and either side to move. For
# one-pawn files the first slot is the pawn; two-pawn profiles distinguish
# KPPK from KPKP. The theorem parameters retain their exact format domains.
# No full four-man generation is performed by proof checking.
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
