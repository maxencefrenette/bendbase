import Base
import ./game.bend as Game
import ./finite_table.bend as Finite

# C describes immutable adapter data at the output and dependency widths.
# Templates specialize callbacks without duplicating affine closures at runtime.
def fill(~C: Nat -> Nat -> Data,
  ~entry: @+width: Nat -> @+low: Nat -> C(width, low) -> Word(width) -> Game.Outcome,
  depth: Nat, +width: Nat, +low: Nat, +context: C(width, low),
  keys: Finite.Table(depth, Word(width))) -> Finite.Table(depth, Game.Outcome):
  match depth keys:
    case 0n key:
      entry(width, low, context, key)
    case 1n++rest Finite.Fork{left, right}:
      a b = fill(~C, ~entry, rest, width, low, context, left) fill(~C, ~entry, rest, width, low, context, right)
      Finite.Fork{a, b}

def fold(rest: List<&2, Game.Outcome>, +turn: Game.Player, first: Game.Outcome) -> Game.Outcome:
  match rest:
    case Nil{}:
      first
    case head <> tail:
      Game.best(turn, first, fold(tail, turn, head))

def bytes(depth: Nat, table: Finite.Table(depth, Game.Outcome)) -> Finite.Table(depth, U32):
  match depth table:
    case 0n outcome:
      Game.byte(outcome)
    case 1n++rest Finite.Fork{left, right}:
      a b = bytes(rest, left) bytes(rest, right)
      Finite.Fork{a, b}
