import Base
import ./dependency_engine.bend as Dependencies
import ./finite_table.bend as Finite

# Structural proofs over the supplied plan/cache, never over chess boards.
def family_get(~D: Data, ~C: Nat -> Data, ~A: Nat -> Data,
  ~solve: @+width: Nat -> C(width) -> D -> A(width),
  depth: Nat, +width: Nat, +context: C(width),
  +descriptors: Finite.Table(depth, D), +key: Word(depth)) ->
  {Finite.get(depth, A(width), key, Dependencies.family(~D, ~C, ~A, ~solve, depth, width, context, descriptors)) ==
   solve(width, context, Finite.get(depth, D, key, descriptors)) : A(width)}:
  match depth descriptors key:
    case 0n descriptor WNil{}:
      {==}
    case 1n+rest Finite.Fork{left, right} WCon{False{}, tail}:
      family_get(~D, ~C, ~A, ~solve, rest, width, context, left, tail)
    case 1n+rest Finite.Fork{left, right} WCon{True{}, tail}:
      family_get(~D, ~C, ~A, ~solve, rest, width, context, right, tail)

# Every completed stage remains accessible after any number of later stages.
# The value is exactly the step applied to its already-completed predecessors.
def history_get(~C: Nat -> Data, ~A: Nat -> Data,
  ~step: @+stage: Nat -> @+width: Nat -> C(width) -> List<&2, A(width)> -> A(width),
  later: Nat, +stage: Nat, +width: Nat, +context: C(width)) ->
  {Dependencies.lookup(later, A(width),
     Dependencies.history(~C, ~A, ~step, Nat.add(later, 1n+stage), width, context)) ==
   Some{step(1n+stage, width, context, Dependencies.history(~C, ~A, ~step, stage, width, context))} : Maybe<&2, A(width)>}:
  match later:
    case 0n:
      {==}
    case 1n+rest:
      history_get(~C, ~A, ~step, rest, stage, width, context)

def count(-A: Data, values: List<&2, A>) -> Nat:
  match values:
    case Nil{}:
      0n
    case head <> tail:
      1n+count(A, tail)

def history_count(~C: Nat -> Data, ~A: Nat -> Data,
  ~step: @+stage: Nat -> @+width: Nat -> C(width) -> List<&2, A(width)> -> A(width),
  stages: Nat, +width: Nat, +context: C(width)) ->
  {count(A(width), Dependencies.history(~C, ~A, ~step, stages, width, context)) == stages : Nat}:
  match stages:
    case 0n:
      {==}
    case 1n++prior:
      %history_count(~C, ~A, ~step, prior, width, context) :
        {1n+count(A(width), Dependencies.history(~C, ~A, ~step, prior, width, context)) == 1n+_ : Nat}
      {==}

def lookup_head(-A: Data, +value: A, +cache: List<&2, A>) ->
  {Dependencies.lookup(0n, A, value <> cache) == Some{value} : Maybe<&2, A>}:
  {==}

def lookup_previous(-A: Data, +offset: Nat, +value: A, +cache: List<&2, A>) ->
  {Dependencies.lookup(1n+offset, A, value <> cache) == Dependencies.lookup(offset, A, cache) : Maybe<&2, A>}:
  {==}

def lookup_missing(-A: Data, offset: Nat) ->
  {Dependencies.lookup(offset, A, Nil{}) == None{} : Maybe<&2, A>}:
  match offset:
    case 0n:
      {==}
    case 1n+rest:
      {==}
