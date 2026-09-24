import Base
import ./game.bend as Game
import ./finite_table.bend as Finite
import ./table_engine.bend as Engine

# Structural induction on the index tree, not enumeration of chess positions.
# Every adapter inherits this exact pointwise meaning of the parallel fill.
def fill_get(~C: Nat -> Nat -> Data,
  ~entry: @+width: Nat -> @+low: Nat -> C(width, low) -> Word(width) -> Game.Outcome,
  depth: Nat, +width: Nat, +low: Nat, +context: C(width, low),
  +keys: Finite.Table(depth, Word(width)), +key: Word(depth)) ->
  {Finite.get(depth, Game.Outcome, key, Engine.fill(~C, ~entry, depth, width, low, context, keys)) ==
   entry(width, low, context, Finite.get(depth, Word(width), key, keys)) : Game.Outcome}:
  match depth keys key:
    case 0n word WNil{}:
      {==}
    case 1n+rest Finite.Fork{left, right} WCon{False{}, tail}:
      fill_get(~C, ~entry, rest, width, low, context, left, tail)
    case 1n+rest Finite.Fork{left, right} WCon{True{}, tail}:
      fill_get(~C, ~entry, rest, width, low, context, right, tail)

def bytes_get(depth: Nat, +table: Finite.Table(depth, Game.Outcome), +key: Word(depth)) ->
  {Finite.get(depth, U32, key, Engine.bytes(depth, table)) ==
   Game.byte(Finite.get(depth, Game.Outcome, key, table)) : U32}:
  match depth table key:
    case 0n value WNil{}:
      {==}
    case 1n+rest Finite.Fork{left, right} WCon{False{}, tail}:
      bytes_get(rest, left, tail)
    case 1n+rest Finite.Fork{left, right} WCon{True{}, tail}:
      bytes_get(rest, right, tail)
