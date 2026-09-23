import Base
import ./rules.bend as Rules

# This is the mathematical content of Black's remaining counter. Each entry is
# one legal successor, including exits from this table (for example K vs K).
# True means that successor has already been established as a White win.
def unresolved(xs: List<&2, Bool>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      match h:
        case True{}:
          unresolved(t)
        case False{}:
          1n+unresolved(t)

def all_winning(xs: List<&2, Bool>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      h && all_winning(t)

def join(xs: List<&2, Bool>, ys: List<&2, Bool>) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      h <> join(t, ys)

def any_winning(xs: List<&2, Bool>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      h || any_winning(t)

# Two vectors of successor facts are related when no established win is lost.
def extends(old: List<&2, Bool>, new: List<&2, Bool>) -> Bool:
  match old new:
    case Nil{} Nil{}:
      True{}
    case Con{a, as} Con{b, bs}:
      (Bool.not(a) || b) && extends(as, bs)
    case _ _:
      False{}

# An empty move list is a loss only if Black is in check (checkmate); the
# other empty case is stalemate. A nonempty list is a loss once all replies
# have become White wins.
def black_forced_loss(check: Bool, xs: List<&2, Bool>) -> Bool:
  match xs:
    case Nil{}:
      check
    case Con{h, t}:
      all_winning(h <> t)

# The reverse search has exactly these three source families: a previous White
# king square, a previous extra-piece square, or a previous Black king square.
def predecessor_shape(previous: Rules.State,
  current: Rules.State) -> Bool:
  match previous current:
    case Rules.State{wk, bk, pc, 0}
         Rules.State{wk2, bk2, pc2, 1}:
      U32.is_eq(bk, bk2) &&
      (U32.is_eq(pc, pc2) || U32.is_eq(wk, wk2))
    case Rules.State{wk, bk, pc, 1}
         Rules.State{wk2, bk2, pc2, 0}:
      U32.is_eq(wk, wk2) && U32.is_eq(pc, pc2)
    case _ _:
      False{}
