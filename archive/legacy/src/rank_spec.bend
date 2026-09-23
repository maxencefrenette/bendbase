import Base
import ./wdl_spec.bend as WDL
import ./clocked_wdl_spec.bend as Clocked

# A proof-level abstraction of a table entry. This does not inspect an array:
# rank is an arbitrary function on game positions. A positive entry bounded
# by n is a proposed White win within n plies.
def PositiveAtMost(~rank: WDL.Game -> Nat, n: Nat,
  +game: WDL.Game) -> Type:
  WDL.Truth(Nat.is_gt(rank(game), 0n)) &
  WDL.Truth(Nat.is_le(rank(game), n))

# The local certificate obligation at horizon n. White exhibits one smaller
# positive successor; Black either is mated or has only such successors.
# Dead-material exits cannot satisfy the obligation.
def Step(~rank: WDL.Game -> Nat, n: Nat,
  +game: WDL.Game) -> Type:
  match game:
    case WDL.KingsOnly{}:
      Empty
    case WDL.BareBishop{}:
      Empty
    case WDL.BareKnight{}:
      Empty
    case WDL.White{kind, wk, bk, pc}:
      &next: WDL.Game ->
        WDL.Truth(WDL.move(game, next)) &
        PositiveAtMost(~rank, n, next)
    case WDL.Black{kind, wk, bk, pc}:
      WDL.BlackMate(kind, wk, bk, pc) |
      (WDL.BlackHasMove(kind, wk, bk, pc) &
        (@next: WDL.Game -> WDL.Truth(WDL.move(game, next)) ->
          PositiveAtMost(~rank, n, next)))

# A bounded certificate says that every positive entry at or below n+1 has
# the appropriate one-ply obligation at n. The theorem using this premise
# quantifies over all positions; it does not enumerate them.
def BoundedCertificate(~rank: WDL.Game -> Nat) -> Type:
  @n: Nat -> @game: WDL.Game ->
    PositiveAtMost(~rank, 1n+n, game) -> Step(~rank, n, game)

def Evidence(~rank: WDL.Game -> Nat, n: Nat,
  +game: WDL.Game) -> Type:
  match n:
    case 0n:
      PositiveAtMost(~rank, 0n, game)
    case 1n+rest:
      Step(~rank, rest, game)

def LocalAt(~rank: WDL.Game -> Nat, value: Nat,
  +game: WDL.Game) -> Type:
  match value:
    case 0n:
      Unit
    case 1n+rest:
      Step(~rank, rest, game)

# This is the direct rank rule checked by the runtime certificate: a positive
# rank's winning successors have smaller positive ranks. The rank function is
# abstract here, and the premise is universally quantified over positions.
def LocalCertificate(~rank: WDL.Game -> Nat) -> Type:
  @game: WDL.Game -> LocalAt(~rank, rank(game), game)

def Positive(~rank: WDL.Game -> Nat, game: WDL.Game) -> Type:
  WDL.Truth(Nat.is_gt(rank(game), 0n))

def ZeroClosedAt(~rank: WDL.Game -> Nat, value: Nat,
  +game: WDL.Game) -> Type:
  match value:
    case 0n:
      WDL.Attractor(~Positive(~rank), game) -> Empty
    case 1n+rest:
      Unit

def ZeroCertificate(~rank: WDL.Game -> Nat) -> Type:
  @game: WDL.Game -> ZeroClosedAt(~rank, rank(game), game)

def ZeroStep(~rank: WDL.Game -> Nat,
  +game: WDL.Game) -> Type:
  match game:
    case WDL.KingsOnly{}:
      Unit
    case WDL.BareBishop{}:
      Unit
    case WDL.BareKnight{}:
      Unit
    case WDL.White{kind, wk, bk, pc}:
      @next: WDL.Game -> WDL.Truth(WDL.move(game, next)) ->
        Positive(~rank, next) -> Empty
    case WDL.Black{kind, wk, bk, pc}:
      (WDL.BlackMate(kind, wk, bk, pc) -> Empty) &
      ((WDL.BlackHasMove(kind, wk, bk, pc) -> Empty) |
        (&next: WDL.Game ->
          WDL.Truth(WDL.move(game, next)) &
          WDL.Truth(Nat.is_eq(rank(next), 0n))))

def ZeroLocalAt(~rank: WDL.Game -> Nat, value: Nat,
  +game: WDL.Game) -> Type:
  match value:
    case 0n:
      ZeroStep(~rank, game)
    case 1n+rest:
      Unit

def ZeroLocalCertificate(~rank: WDL.Game -> Nat) -> Type:
  @game: WDL.Game -> ZeroLocalAt(~rank, rank(game), game)

# A pawn table can lead into a promoted-piece table. The offset makes a
# positive pawn rank strictly higher than every promoted-piece rank bounded
# by 49, while preserving zero as draw.
def phase_rank(pawn: Bool, raw: Nat) -> Nat:
  match pawn raw:
    case False{} value:
      value
    case True{} 0n:
      0n
    case True{} Succ{rest}:
      Nat.add(50n, 1n+rest)

def lifted_rank(~raw: WDL.Game -> Nat, game: WDL.Game) -> Nat:
  match game:
    case WDL.KingsOnly{}:
      raw(WDL.KingsOnly{})
    case WDL.BareBishop{}:
      raw(WDL.BareBishop{})
    case WDL.BareKnight{}:
      raw(WDL.BareKnight{})
    case WDL.White{+kind, +wk, +bk, +pc}:
      phase_rank(U32.is_eq(kind, 4),
        raw(WDL.White{kind, wk, bk, pc}))
    case WDL.Black{+kind, +wk, +bk, +pc}:
      phase_rank(U32.is_eq(kind, 4),
        raw(WDL.Black{kind, wk, bk, pc}))

def ExactClockZero(~rank: WDL.Game -> Nat,
  +game: WDL.Game) -> Type:
  (Positive(~rank, game) & Clocked.ClockZeroWhiteWin(game)) |
  (WDL.Truth(Nat.is_eq(rank(game), 0n)) &
    (Clocked.ClockZeroWhiteWin(game) -> Empty) &
    (Clocked.ClockZeroBlackWin(game) -> Empty))
