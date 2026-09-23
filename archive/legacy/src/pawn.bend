import Base
import ./rules.bend as Rules
import ./retrograde.bend as Retro

type Promoted is Type:
  Promoted{queen: Array<U32>, rook: Array<U32>,
    bishop: Array<U32>, knight: Array<U32>}

type PawnWork is Type:
  PawnWork{promoted: Promoted, work: Retro.Work}

def read.knight(queen: Array<U32>, rook: Array<U32>, bishop: Array<U32>,
  prior: Bool, read: Array<U32> & U32) -> Promoted & Bool:
  match read:
    case (knight, value):
      (Promoted{queen, rook, bishop, knight},
        prior || U32.is_ne(value, 0))

def read.bishop(queen: Array<U32>, rook: Array<U32>,
  knight: Array<U32>, +i: U32, prior: Bool,
  read: Array<U32> & U32) -> Promoted & Bool:
  match read:
    case (bishop, value):
      read.knight(queen, rook, bishop,
        prior || U32.is_ne(value, 0), knight[i])

def read.rook(queen: Array<U32>, bishop: Array<U32>,
  knight: Array<U32>, +i: U32, prior: Bool,
  read: Array<U32> & U32) -> Promoted & Bool:
  match read:
    case (rook, value):
      read.bishop(queen, rook, knight, i,
        prior || U32.is_ne(value, 0), bishop[i])

def read.queen(rook: Array<U32>, bishop: Array<U32>,
  knight: Array<U32>, +i: U32, read: Array<U32> & U32) ->
  Promoted & Bool:
  match read:
    case (queen, value):
      read.rook(queen, bishop, knight, i, U32.is_ne(value, 0), rook[i])

def promotion_wins(promoted: Promoted, +i: U32) -> Promoted & Bool:
  match promoted:
    case Promoted{queen, rook, bishop, knight}:
      read.queen(rook, bishop, knight, i, queen[i])

def mark_promotion.if(promoted: Promoted, work: Retro.Work,
  state: Rules.State, won: Bool) -> PawnWork:
  match won:
    case True{}:
      PawnWork{promoted, Retro.mark(work, state)}
    case False{}:
      PawnWork{promoted, work}

def seed.read(work: Retro.Work, state: Rules.State,
  read: Promoted & Bool) -> PawnWork:
  match read:
    case (promoted, won):
      mark_promotion.if(promoted, work, state, won)

def seed.promotion(pw: PawnWork,
  +wk: U32, +bk: U32, +pc: U32) -> PawnWork:
  match pw:
    case PawnWork{promoted, work}:
      +target = (pc + 8 : U32)
      promoted_i = Rules.index(Rules.State{wk, bk, target, 1})
      seed.read(work, Rules.State{wk, bk, pc, 0},
        promotion_wins(promoted, promoted_i))

def seed.if(pw: PawnWork,
  wk: U32, bk: U32, pc: U32, can_promote: Bool) -> PawnWork:
  match can_promote:
    case True{}:
      seed.promotion(pw, wk, bk, pc)
    case False{}:
      pw

def seed.state(pw: PawnWork, s: Rules.State) -> PawnWork:
  match s:
    case Rules.State{+wk, +bk, +pc, 0}:
      can_promote = Rules.pawn_can_promote(wk, bk, pc)
      seed.if(pw, wk, bk, pc, can_promote)
    case _:
      pw

def seed.step(pw: PawnWork, +i: U32) -> PawnWork:
  seed.state(pw, Rules.decode(i))

def seed.go(fuel: Nat, +i: U32, pw: PawnWork) -> PawnWork:
  match fuel:
    case 0n:
      pw
    case 1n+rest:
      seed.go(rest, (i + 1 : U32), seed.step(pw, i))

def solve.fin(pw: PawnWork) -> Promoted & Array<U32>:
  match pw:
    case PawnWork{promoted, work}:
      (promoted, Retro.solve.fin(Retro.propagate.go(524288n, 4, work)))

def solve(promoted: Promoted) -> Promoted & Array<U32>:
  solve.fin(seed.go(524288n, 0, PawnWork{promoted, Retro.init(4)}))
