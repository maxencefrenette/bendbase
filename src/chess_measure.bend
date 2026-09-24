import Base
import ./position.bend as P
import ./game.bend as Game
import ./chess.bend as Chess
import ./pawnless_chess.bend as Three
import ./pawn_distance.bend as PawnDistance

# Ranks remaining, not the number of pawn moves: a double push consumes two.
# The three most significant square bits are the rank. Complementing them
# computes 7-rank for White; Black uses rank itself. Files never contribute.
def distance(+owner: Game.Player, square: Word(6n)) -> Nat:
  PawnDistance.distance(owner, square)

def extra(owner: Game.Player, kind: P.PieceKind, square: Word(6n)) -> Nat:
  match kind:
    case P.Pawn{}:
      distance(owner, square)
    case P.Piece{kind}:
      0n

def weight(man: P.Man) -> Nat:
  match man:
    case P.Man{owner, kind, square}:
      1n+extra(owner, kind, square)

def men(pieces: List<&2, P.Man>) -> Nat:
  match pieces:
    case Nil{}:
      0n
    case head <> tail:
      Nat.add(weight(head), men(tail))

def position(board: P.Position) -> Nat:
  match board:
    case P.Position{turn, wk, bk, pieces, ep, target}:
      2n+men(pieces)

# Structural natural-number order: unlike a machine integer this cannot wrap.
def Le(a: Nat, b: Nat) -> Type:
  match a b:
    case 0n _:
      Unit
    case 1n+rest 0n:
      Empty
    case 1n+x 1n+y:
      Le(x, y)

def Lt(a: Nat, b: Nat) -> Type:
  Le(1n+a, b)

# Local obligation for the moving pawns, separate from the arbitrary-length
# list induction. Non-pawns need no obligation. This is NOT a legality guard.
# Establishing it from Chess.legal remains the geometry/uniqueness bridge.
def PawnProgress(moving: Bool, +owner: Game.Player, kind: P.PieceKind,
  at: Word(6n), dest: Word(6n)) -> Type:
  match moving kind:
    case True{} P.Pawn{}:
      Lt(distance(owner, dest), distance(owner, at))
    case _ _:
      Unit

def Progress(pieces: List<&2, P.Man>, +from: Word(6n), +dest: Word(6n)) -> Type:
  match pieces:
    case Nil{}:
      Unit
    case P.Man{owner, kind, at} <> tail:
      PawnProgress(Chess.equal(at, from), owner, kind, at, dest) & Progress(tail, from, dest)

def MoveProgress(board: P.Position, move: Chess.Action) -> Type:
  match board move:
    case P.Position{turn, wk, bk, pieces, ep, target} Chess.Action{from, dest, choice}:
      Progress(pieces, from, dest)

def moved(+moving: Bool, +owner: Game.Player, kind: P.PieceKind, at: Word(6n), +dest: Word(6n), choice: Three.Material) -> P.Man:
  P.Man{owner, Chess.moved_kind(moving, owner, kind, dest, choice), Bool.pick(Word(6n), moving, dest, at)}

def moving_pawn(moving: Bool, kind: P.PieceKind) -> Bool:
  match kind:
    case P.Pawn{}:
      moving
    case P.Piece{kind}:
      False{}

# True exactly when this list update removes a man or moves a pawn.
def changes(pieces: List<&2, P.Man>, +from: Word(6n), +dest: Word(6n), +ep: Bool, +victim: Word(6n)) -> Bool:
  match pieces:
    case Nil{}:
      False{}
    case P.Man{owner, +kind, +at} <> tail:
      (Chess.equal(at, dest) || (ep && Chess.equal(at, victim))) ||
        (moving_pawn(Chess.equal(at, from), kind) || changes(tail, from, dest, ep, victim))

def Bound(strict: Bool, after: Nat, before: Nat) -> Type:
  match strict:
    case False{}:
      Le(after, before)
    case True{}:
      Lt(after, before)
