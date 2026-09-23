import Base

def append(-m: Nat, n: Nat, word: Word(n), tail: Word(m)) -> Word(Nat.add(n, m)):
  match n word:
    case 0n WNil{}:
      tail
    case 1n+rest WCon{bit, more}:
      WCon{bit, append(m, rest, more, tail)}

def split.prepend(-n: Nat, -m: Nat, bit: Bool, pair: Word(n) & Word(m)) -> Word(1n+n) & Word(m):
  match pair:
    case Tuple{low, high}:
      (WCon{bit, low}, high)

def split(-m: Nat, n: Nat, word: Word(Nat.add(n, m))) -> Word(n) & Word(m):
  match n word:
    case 0n word:
      (WNil{}, word)
    case 1n+rest WCon{bit, more}:
      split.prepend(rest, m, bit, split(m, rest, more))
