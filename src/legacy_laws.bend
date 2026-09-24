import Base
import ./game.bend as Game
import ./pawnless_chess.bend as Chess
import ./pawnless_index.bend as Index
import ./pawn_chess.bend as Pawn
import ./material_chess.bend as Material
import ./four_index.bend as FourIndex
import ./one_pawn_chess.bend as OnePawn
import ./two_pawn_chess.bend as TwoPawn
import ./position.bend as Position
import ./position_legacy.bend as PositionLegacy

# Supporting laws for existing specialized generators and representation
# bridges. The public byte-correctness contracts remain in ../LAWS.bend.
# Bridges establish lossless conversion, not equivalence of all independently
# defined legal-move predicates. Material.move rules cover arbitrary pawnless
# lists; captures strictly decrease count and quiet moves preserve it.
# Specialized one-/two-pawn move laws retain their action widths and domains.
# No castling is modeled. Existing four-man roots have no EP rights, but
# two-pawn continuations include EP. No full table is evaluated by this proof.
# Every law here is discharged by ../PROOF.bend.

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

law material_three_man_roundtrip:
  for +material: Chess.Material
  for +board: Chess.Board
  {Material.to_three(Material.from_three(material, board)) == Material.Single{material, board} : Material.Projection}

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

law four_position_index_roundtrip:
  for +board: FourIndex.Board
  {FourIndex.decode(FourIndex.encode(board)) == board : FourIndex.Board}

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
