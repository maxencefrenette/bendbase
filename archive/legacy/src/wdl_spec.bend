import Base
import ./rules.bend as Rules
import ./position.bend as Position

# A proof-level game state has an explicit turn. This avoids treating an
# out-of-range U32 turn as a chess position. The generator's U32 encoding must
# eventually be proved to refine this representation.
type Game is Data:
  KingsOnly{}
  BareBishop{}
  BareKnight{}
  White{kind: U32, wk: U32, bk: U32, pc: U32}
  Black{kind: U32, wk: U32, bk: U32, pc: U32}

# Three-man material with only a bishop or knight is terminal insufficient
# material, regardless of square placement or whose turn it is. The table
# mapping sends those classes to these two bare variants, not to White/Black.
def material_game(kind: U32, +turn: U32, +wk: U32,
  +bk: U32, +pc: U32) -> Game:
  match kind:
    case 2:
      BareBishop{}
    case 3:
      BareKnight{}
    case _:
      match turn:
        case 0:
          White{kind, wk, bk, pc}
        case _:
          Black{kind, wk, bk, pc}

def Truth(b: Bool) -> Data:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def promotion(+wk: U32, +bk: U32, +pc: U32,
  +kind: U32, +wk2: U32, +bk2: U32, +pc2: U32) -> Bool:
  Rules.pawn_can_promote(wk, bk, pc) &&
  (U32.is_lt(kind, 4) &&
    U32.is_eq(wk, wk2) && U32.is_eq(bk, bk2) &&
    U32.is_eq(pc2, (pc + 8 : U32)) &&
    Rules.valid(kind, Rules.State{wk2, bk2, pc2, 1}))

def move(+from: Game, +to: Game) -> Bool:
  match from to:
    case White{+kind, +wk, +bk, +pc} BareBishop{}:
      U32.is_eq(kind, 4) &&
      promotion(wk, bk, pc, 2, wk, bk, (pc + 8 : U32))
    case White{+kind, +wk, +bk, +pc} BareKnight{}:
      U32.is_eq(kind, 4) &&
      promotion(wk, bk, pc, 3, wk, bk, (pc + 8 : U32))
    case White{+kind, +wk, +bk, +pc}
         Black{+kind2, +wk2, +bk2, +pc2}:
      (U32.is_eq(kind, kind2) &&
        Rules.move_to(kind, Rules.State{wk, bk, pc, 0},
          Rules.State{wk2, bk2, pc2, 1})) ||
      (U32.is_eq(kind, 4) && U32.is_lt(kind2, 2) &&
        promotion(wk, bk, pc, kind2, wk2, bk2, pc2))
    case Black{+kind, +wk, +bk, +pc}
         White{+kind2, +wk2, +bk2, +pc2}:
      U32.is_eq(kind, kind2) &&
      Rules.move_to(kind, Rules.State{wk, bk, pc, 1},
        Rules.State{wk2, bk2, pc2, 0})
    case Black{+kind, +wk, +bk, +pc} KingsOnly{}:
      Rules.valid(kind, Rules.State{wk, bk, pc, 1}) &&
      Rules.black_move(kind, wk, bk, pc, pc)
    case _ _:
      False{}

def BlackHasMove(+kind: U32, +wk: U32, +bk: U32, +pc: U32) -> Type:
  &next: Game -> Truth(move(Black{kind, wk, bk, pc}, next))

# No legal successor is a quantified proposition, not a 64-square scan.
def BlackMate(+kind: U32, +wk: U32, +bk: U32, +pc: U32) -> Type:
  Truth(Rules.valid(kind, Rules.State{wk, bk, pc, 1})) &
  Truth(Rules.attacks(kind, pc, bk, wk)) &
  (BlackHasMove(kind, wk, bk, pc) -> Empty)

def WhiteHasMove(+kind: U32, +wk: U32, +bk: U32,
  +pc: U32) -> Type:
  &next: Game -> Truth(move(White{kind, wk, bk, pc}, next))

# Black has only a king. A valid White-to-move state cannot have its king in
# check from that king, so this terminal condition is uninhabited.
def WhiteMate(+kind: U32, +wk: U32, +bk: U32,
  +pc: U32) -> Type:
  Truth(Rules.valid(kind, Rules.State{wk, bk, pc, 0})) &
  Truth(Position.kings_touch(wk, bk)) &
  (WhiteHasMove(kind, wk, bk, pc) -> Empty)

# This is a finite-horizon forcing-game semantics, not a certificate checker.
# KingsOnly is never winning. Stalemate is excluded by has_move; checkmate is
# an immediate White win. Promotion is an ordinary move to another material
# class, so the semantic horizon counts through it.
def WinWithin(n: Nat, +game: Game) -> Type:
  match n game:
    case 0n Black{kind, wk, bk, pc}:
      BlackMate(kind, wk, bk, pc)
    case 0n _:
      Empty
    case 1n+rest White{kind, wk, bk, pc}:
      &next: Game ->
        Truth(move(White{kind, wk, bk, pc}, next)) &
        WinWithin(rest, next)
    case 1n+rest Black{kind, wk, bk, pc}:
      BlackMate(kind, wk, bk, pc) |
      (BlackHasMove(kind, wk, bk, pc) &
        (@next: Game ->
          Truth(move(Black{kind, wk, bk, pc}, next)) ->
          WinWithin(rest, next)))
    case 1n+rest KingsOnly{}:
      Empty
    case 1n+rest BareBishop{}:
      Empty
    case 1n+rest BareKnight{}:
      Empty

def WhiteCanForceWin(game: Game) -> Type:
  &plies: Nat -> WinWithin(plies, game)

def BlackWinWithin(n: Nat, +game: Game) -> Type:
  match n game:
    case 0n White{kind, wk, bk, pc}:
      WhiteMate(kind, wk, bk, pc)
    case 0n _:
      Empty
    case 1n+rest Black{kind, wk, bk, pc}:
      &next: Game ->
        Truth(move(Black{kind, wk, bk, pc}, next)) &
        BlackWinWithin(rest, next)
    case 1n+rest White{kind, wk, bk, pc}:
      WhiteMate(kind, wk, bk, pc) |
      (WhiteHasMove(kind, wk, bk, pc) &
        (@next: Game ->
          Truth(move(White{kind, wk, bk, pc}, next)) ->
          BlackWinWithin(rest, next)))
    case 1n+rest KingsOnly{}:
      Empty
    case 1n+rest BareBishop{}:
      Empty
    case 1n+rest BareKnight{}:
      Empty

# The one-ply White-win attractor of an arbitrary proposition P. A set P is
# closed when every position in Attractor(P) is already in P. This is a
# symbolic operator over games, not an enumeration of board positions.
def Attractor(~P: Game -> Type, +game: Game) -> Type:
  match game:
    case KingsOnly{}:
      Empty
    case BareBishop{}:
      Empty
    case BareKnight{}:
      Empty
    case White{kind, wk, bk, pc}:
      &next: Game ->
        Truth(move(White{kind, wk, bk, pc}, next)) & P(next)
    case Black{kind, wk, bk, pc}:
      BlackMate(kind, wk, bk, pc) |
      (BlackHasMove(kind, wk, bk, pc) &
        (@next: Game ->
          Truth(move(Black{kind, wk, bk, pc}, next)) -> P(next)))
