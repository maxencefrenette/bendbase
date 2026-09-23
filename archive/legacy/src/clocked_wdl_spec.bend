import Base
import ./wdl_spec.bend as WDL

# Pawn moves and captures reset the halfmove clock. In this normalized
# three-man game, Black's only capture exits into KingsOnly.
def zeroing(+from: WDL.Game, +to: WDL.Game) -> Bool:
  match from to:
    case WDL.White{+kind, wk, bk, +pc}
         WDL.Black{kind2, wk2, bk2, +pc2}:
      U32.is_eq(kind, 4) && U32.is_ne(pc, pc2)
    case WDL.White{kind, wk, bk, pc} WDL.BareBishop{}:
      True{}
    case WDL.White{kind, wk, bk, pc} WDL.BareKnight{}:
      True{}
    case WDL.Black{kind, wk, bk, pc} WDL.KingsOnly{}:
      True{}
    case _ _:
      False{}

def next_clock.if(clock: Nat, zero: Bool) -> Nat:
  match zero:
    case True{}:
      0n
    case False{}:
      1n+clock

def next_clock(clock: Nat, +from: WDL.Game, +to: WDL.Game) -> Nat:
  next_clock.if(clock, zeroing(from, to))

# The user's tablebase convention treats clock 100 as a terminal draw: under
# perfect play, the defender claims it rather than continuing a lost game.
# This abstracts away the optional-claim mechanics of over-the-board chess.
# Checkmate on the move reaching 100 takes precedence: BlackMate remains
# available even when the clock is 100.
def WinWithin(n: Nat, clock: Nat, +game: WDL.Game) -> Type:
  match n game:
    case 0n WDL.Black{kind, wk, bk, pc}:
      WDL.BlackMate(kind, wk, bk, pc)
    case 0n _:
      Empty
    case 1n+rest WDL.White{kind, wk, bk, pc}:
      WDL.Truth(Nat.is_lt(clock, 100n)) &
      (&next: WDL.Game ->
        WDL.Truth(WDL.move(game, next)) &
        WinWithin(rest, next_clock(clock, game, next), next))
    case 1n+rest WDL.Black{kind, wk, bk, pc}:
      WDL.BlackMate(kind, wk, bk, pc) |
      (WDL.Truth(Nat.is_lt(clock, 100n)) &
        WDL.BlackHasMove(kind, wk, bk, pc) &
        (@next: WDL.Game -> WDL.Truth(WDL.move(game, next)) ->
          WinWithin(rest, next_clock(clock, game, next), next)))
    case 1n+rest WDL.KingsOnly{}:
      Empty
    case 1n+rest WDL.BareBishop{}:
      Empty
    case 1n+rest WDL.BareKnight{}:
      Empty

def ClockZeroWhiteWin(game: WDL.Game) -> Type:
  &plies: Nat -> WinWithin(plies, 0n, game)

def BlackWinWithin(n: Nat, clock: Nat, +game: WDL.Game) -> Type:
  match n game:
    case 0n WDL.White{kind, wk, bk, pc}:
      WDL.WhiteMate(kind, wk, bk, pc)
    case 0n _:
      Empty
    case 1n+rest WDL.Black{kind, wk, bk, pc}:
      WDL.Truth(Nat.is_lt(clock, 100n)) &
      (&next: WDL.Game ->
        WDL.Truth(WDL.move(game, next)) &
        BlackWinWithin(rest, next_clock(clock, game, next), next))
    case 1n+rest WDL.White{kind, wk, bk, pc}:
      WDL.WhiteMate(kind, wk, bk, pc) |
      (WDL.Truth(Nat.is_lt(clock, 100n)) &
        WDL.WhiteHasMove(kind, wk, bk, pc) &
        (@next: WDL.Game -> WDL.Truth(WDL.move(game, next)) ->
          BlackWinWithin(rest, next_clock(clock, game, next), next)))
    case 1n+rest WDL.KingsOnly{}:
      Empty
    case 1n+rest WDL.BareBishop{}:
      Empty
    case 1n+rest WDL.BareKnight{}:
      Empty

def ClockZeroBlackWin(game: WDL.Game) -> Type:
  &plies: Nat -> BlackWinWithin(plies, 0n, game)

def DrawAtClockZero(game: WDL.Game) -> Type:
  (ClockZeroWhiteWin(game) -> Empty) &
  (ClockZeroBlackWin(game) -> Empty)

# A structural safety budget for an n-ply strategy. At each ply the clock is
# below 100, and both possible clock updates (increment or zeroing reset)
# retain the budget for the remaining plies. This is a proposition, not a
# traversal of board positions.
def Safe(n: Nat, clock: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+rest:
      WDL.Truth(Nat.is_lt(clock, 100n)) &
      Safe(rest, 1n+clock) & Safe(rest, 0n)

type Timed is Data:
  Timed{clock: Nat, game: WDL.Game}

# One-ply attractor of a symbolic set of clocked positions.
def Attractor(~P: Timed -> Type, timed: Timed) -> Type:
  match timed:
    case Timed{clock, WDL.White{kind, wk, bk, pc}}:
      WDL.Truth(Nat.is_lt(clock, 100n)) &
      (&next: WDL.Game ->
        WDL.Truth(WDL.move(WDL.White{kind, wk, bk, pc}, next)) &
        P(Timed{next_clock(clock, WDL.White{kind, wk, bk, pc}, next),
          next}))
    case Timed{clock, WDL.Black{kind, wk, bk, pc}}:
      WDL.BlackMate(kind, wk, bk, pc) |
      (WDL.Truth(Nat.is_lt(clock, 100n)) &
        WDL.BlackHasMove(kind, wk, bk, pc) &
        (@next: WDL.Game ->
          WDL.Truth(WDL.move(WDL.Black{kind, wk, bk, pc}, next)) ->
          P(Timed{next_clock(clock, WDL.Black{kind, wk, bk, pc}, next),
            next})))
    case Timed{clock, WDL.KingsOnly{}}:
      Empty
    case Timed{clock, WDL.BareBishop{}}:
      Empty
    case Timed{clock, WDL.BareKnight{}}:
      Empty
