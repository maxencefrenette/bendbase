import Base
import ./chess_cache_invariant.bend as I
import ./chess_cache_invariant_proof.bend as Proof
import ./chess_solver.bend as Compile
import ./chess_solver_proof.bend as CompileProof
import ./table_cache_proof.bend as TableProof
import ./material_directory.bend as Directory
import ./material_cache.bend as Registry
import ./component_cache.bend as Stages
import ./position.bend as P
import ./game.bend as Game

def unpack(value: Maybe<&2, List<&2, Stages.Stage>>) -> List<&2, Stages.Stage>:
  match value:
    case None{}:
      Nil{}
    case Some{stages}:
      stages

# unpack is a proof observation only, never used by the generator. Applying
# it to an equality between two Some constructors establishes injectivity.
def same(+left: List<&2, Stages.Stage>, +right: List<&2, Stages.Stage>,
  exact: {Some{left} == Some{right} : Maybe<&2, List<&2, Stages.Stage>>}) -> {left == right : List<&2, Stages.Stage>}:
  Equal.cong(Maybe<&2, List<&2, Stages.Stage>>, List<&2, Stages.Stage>, value => unpack(value), Some{left}, Some{right}, exact)

def completed(~expected: P.Position -> Game.Outcome, ~limit: Nat, ~sound: I.StageRule(~expected, limit),
  +count: Nat, +capacity: Nat, +previous: List<&2, Stages.Stage>, +entries: Maybe<&2, List<&2, Registry.Named>>, +result: List<&2, Stages.Stage>,
  old: I.Correct(~expected, count, capacity, previous),
  built: {Compile.directory(Directory.names(capacity), 1n+count, limit, previous) == entries : Maybe<&2, List<&2, Registry.Named>>},
  exact: {Compile.completed(1n+count, entries, previous) == Some{result} : Maybe<&2, List<&2, Stages.Stage>>}) ->
  I.Correct(~expected, 1n+count, capacity, result):
  match entries:
    case None{}:
      TableProof.absurd(I.Correct(~expected, 1n+count, capacity, result), CompileProof.impossible(List<&2, Stages.Stage>, result, exact))
    case Some{entries}:
      %same(Stages.Stage{1n+count, entries} <> previous, result, exact) : I.Correct(~expected, 1n+count, capacity, _)
      Proof.step(~expected, count, capacity, entries, previous, old,
        prior => sound(count)(capacity)(previous)(entries)(prior)(built))

def next(~expected: P.Position -> Game.Outcome, ~limit: Nat, ~sound: I.StageRule(~expected, limit),
  +count: Nat, +capacity: Nat, +previous: Maybe<&2, List<&2, Stages.Stage>>, +result: List<&2, Stages.Stage>,
  exact: {Compile.next(1n+count, capacity, limit, previous) == Some{result} : Maybe<&2, List<&2, Stages.Stage>>},
  recurse: @+stages: List<&2, Stages.Stage> -> {previous == Some{stages} : Maybe<&2, List<&2, Stages.Stage>>} -> I.Correct(~expected, count, capacity, stages)) ->
  I.Correct(~expected, 1n+count, capacity, result):
  match previous:
    case None{}:
      TableProof.absurd(I.Correct(~expected, 1n+count, capacity, result), CompileProof.impossible(List<&2, Stages.Stage>, result, exact))
    case Some{previous}:
      completed(~expected, ~limit, ~sound, count, capacity, previous, Compile.directory(Directory.names(capacity), 1n+count, limit, previous), result,
        recurse(previous)({==}), {==}, exact)

# Induction over the REAL fallible generator. No table values are supplied by
# a second evaluator. The StageRule premise is explicit: this theorem does not
# itself discharge component WDL correctness or prove generation succeeds.
def generated(~expected: P.Position -> Game.Outcome, ~limit: Nat, ~sound: I.StageRule(~expected, limit),
  +count: Nat, +capacity: Nat, +result: List<&2, Stages.Stage>,
  exact: {Compile.generate(count, capacity, limit) == Some{result} : Maybe<&2, List<&2, Stages.Stage>>}) ->
  I.Correct(~expected, count, capacity, result):
  match count:
    case 0n:
      %same(Nil{}, result, exact) : I.Correct(~expected, 0n, capacity, _)
      Proof.empty(~expected, capacity)
    case 1n++prior:
      next(~expected, ~limit, ~sound, prior, capacity, Compile.generate(prior, capacity, limit), result, exact,
        +previous => built => generated(~expected, ~limit, ~sound, prior, capacity, previous, built))
