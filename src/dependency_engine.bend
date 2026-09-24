import Base
import ./finite_table.bend as Finite

# Completed components, newest first. The engine knows neither piece kinds
# nor pawn ranks. A miss is explicit; it is never silently a chess draw.
def lookup(offset: Nat, -A: Data, cache: List<&2, A>) -> Maybe<&2, A>:
  match offset cache:
    case _ Nil{}:
      None{}
    case 0n table <> tail:
      Some{table}
    case 1n+rest table <> tail:
      lookup(rest, A, tail)

# Callers must justify any fallback at their chess boundary. The general
# lookup above retains failure, so it can also be used by strict resolvers.
def or_else(-A: Data, fallback: A, found: Maybe<&2, A>) -> A:
  match found:
    case None{}:
      fallback
    case Some{table}:
      table

# Independent components are solved in parallel; the descriptor domain can
# have any size and is not restricted to Q/R/B/N or three-man tables.
def family(~D: Data, ~C: Nat -> Data, ~A: Nat -> Data,
  ~solve: @+width: Nat -> C(width) -> D -> A(width),
  depth: Nat, +width: Nat, +context: C(width), descriptors: Finite.Table(depth, D)) ->
  Finite.Table(depth, A(width)):
  match depth descriptors:
    case 0n descriptor:
      solve(width, context, descriptor)
    case 1n++rest Finite.Fork{left, right}:
      a b = family(~D, ~C, ~A, ~solve, rest, width, context, left) family(~D, ~C, ~A, ~solve, rest, width, context, right)
      Finite.Fork{a, b}

# Solve each dependency stratum once, after all earlier strata. The step
# receives the completed cache, not a recursive evaluator. Chess adapters
# must prove that reset edges only consult these completed dependencies.
def history(~C: Nat -> Data, ~A: Nat -> Data,
  ~step: @+stage: Nat -> @+width: Nat -> C(width) -> List<&2, A(width)> -> A(width),
  stages: Nat, +width: Nat, +context: C(width)) -> List<&2, A(width)>:
  match stages:
    case 0n:
      Nil{}
    case 1n++prior:
      +completed = history(~C, ~A, ~step, prior, width, context)
      step(1n+prior, width, context, completed) <> completed
