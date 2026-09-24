import Base
import ./game.bend as Game
import ./finite_table.bend as Finite
import ./table_cache.bend as Cache

def exact(+width: Nat, +key: Word(width), +table: Finite.Table(width, Game.Outcome)) ->
  {Cache.lookup(width, key, Cache.Entry{width, table}) == Some{Finite.get(width, Game.Outcome, key, table)} : Maybe<&2, Game.Outcome>}:
  match width key table:
    case 0n WNil{} value:
      {==}
    case 1n+rest WCon{False{}, tail} Finite.Fork{left, right}:
      exact(rest, tail, left)
    case 1n+rest WCon{True{}, tail} Finite.Fork{left, right}:
      exact(rest, tail, right)

def fallback_unused(+width: Nat, +key: Word(width), +table: Finite.Table(width, Game.Outcome), +fallback: Game.Outcome) ->
  {Cache.value(Cache.lookup(width, key, Cache.Entry{width, table}), fallback) == Finite.get(width, Game.Outcome, key, table) : Game.Outcome}:
  %exact(width, key, table) :
    {Cache.value(Cache.lookup(width, key, Cache.Entry{width, table}), fallback) == Cache.value(_, fallback) : Game.Outcome}
  {==}

# A successful lookup necessarily consumed exactly the stored width.
def present(found: Maybe<&2, Game.Outcome>) -> Type:
  match found:
    case None{}:
      Empty
    case Some{result}:
      Unit

def none_some(+result: Game.Outcome, found: {None{} == Some{result} : Maybe<&2, Game.Outcome>}) -> Empty:
  %Equal.sym(Maybe<&2, Game.Outcome>, None{}, Some{result}, found) : present(_)
  Unit{}

def absurd(-A: Type, impossible: Empty) -> A:
  match impossible:

def width_matches(+depth: Nat, +width: Nat, +key: Word(width), +table: Finite.Table(depth, Game.Outcome),
  +result: Game.Outcome, found: {Cache.read(depth, width, key, table) == Some{result} : Maybe<&2, Game.Outcome>}) ->
  {depth == width : Nat}:
  match depth width key table:
    case 0n 0n WNil{} value:
      {==}
    case 0n 1n+rest word value:
      absurd({0n == 1n+rest : Nat}, none_some(result, found))
    case 1n+rest 0n WNil{} table:
      absurd({1n+rest == 0n : Nat}, none_some(result, found))
    case 1n++rest 1n++more WCon{False{}, tail} Finite.Fork{left, right}:
      %width_matches(rest, more, tail, left, result, found) : {1n+rest == 1n+_ : Nat}
      {==}
    case 1n++rest 1n++more WCon{True{}, tail} Finite.Fork{left, right}:
      %width_matches(rest, more, tail, right, result, found) : {1n+rest == 1n+_ : Nat}
      {==}
