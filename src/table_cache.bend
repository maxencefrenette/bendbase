import Base
import ./game.bend as Game
import ./finite_table.bend as Finite

# A dependency family can contain completed tables of different sizes.
# Packing retains the actual width; querying never pads or truncates a key.
type Entry is Data:
  Entry{width: Nat, table: Finite.Table(width, Game.Outcome)}

def read(depth: Nat, width: Nat, key: Word(width), table: Finite.Table(depth, Game.Outcome)) -> Maybe<&2, Game.Outcome>:
  match depth width key table:
    case 0n 0n WNil{} value:
      Some{value}
    case 0n 1n+rest word value:
      None{}
    case 1n+rest 0n WNil{} table:
      None{}
    case 1n+rest 1n+more WCon{False{}, tail} Finite.Fork{left, right}:
      read(rest, more, tail, left)
    case 1n+rest 1n+more WCon{True{}, tail} Finite.Fork{left, right}:
      read(rest, more, tail, right)

def lookup(width: Nat, key: Word(width), entry: Entry) -> Maybe<&2, Game.Outcome>:
  match entry:
    case Entry{depth, table}:
      read(depth, width, key, table)

# Explicit compatibility policy for legacy adapters; their WDL proofs show
# all queried entries have the right width. New resolvers should use lookup
# and propagate None rather than treating a missing dependency as a draw.
def value(found: Maybe<&2, Game.Outcome>, fallback: Game.Outcome) -> Game.Outcome:
  match found:
    case None{}:
      fallback
    case Some{result}:
      result

def Family(width: Nat) -> Data:
  Entry
