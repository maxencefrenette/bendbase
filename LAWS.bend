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
