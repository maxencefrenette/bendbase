import Base
import ./game.bend as Game
import ./clock_solver.bend as Solver
import ./table_engine.bend as Engine
import ./table_engine_proof.bend as EngineProof
import ./finite_table.bend as Finite
import ./finite_table_proof.bend as FiniteProof
import ./pawnless_tables_proof.bend as Lemmas
import ./pawnless_chess.bend as Three

def lookup(+width: Nat, +graph: Finite.Table(width, Solver.Node<width>),
  +phase: Solver.Layer<width>, +key: Word(width)) ->
  {Finite.get(width, Game.Outcome, key, Solver.layer(width, graph, phase)) ==
   Solver.at(width, phase, Finite.get(width, Solver.Node<width>, key, graph)) : Game.Outcome}:
  %FiniteProof.keys_get(width, key) :
    {Finite.get(width, Game.Outcome, key, Solver.layer(width, graph, phase)) ==
     Solver.at(width, phase, Finite.get(width, Solver.Node<width>, _, graph)) : Game.Outcome}
  EngineProof.fill_get(~Solver.Family, ~Solver.entry, width, width, 0n,
    Solver.Context{graph, phase}, Finite.keys(width), key)

def assemble_evaluate(+width: Nat, +node: Solver.Node<width>, +trees: List<&2, Game.Tree>) ->
  {Solver.combine(width, node, Lemmas.outcomes(trees)) == Game.evaluate(Solver.assemble(width, node, trees)) : Game.Outcome}:
  match node trees:
    case Solver.Terminal{result} _:
      {==}
    case Solver.Choice{turn, children} Nil{}:
      {==}
    case Solver.Choice{+turn, children} +head <> +tail:
      Equal.sym(Game.Outcome, Game.evaluate(Three.choices(tail, turn, head)),
        Engine.fold(Lemmas.outcomes(tail), turn, Game.evaluate(head)), Lemmas.choices_evaluate(tail, turn, head))

def step(+remaining: Nat, +width: Nat, +graph: Finite.Table(width, Solver.Node<width>), +key: Word(width),
  children:
    {Solver.values(width, Solver.children(width, Finite.get(width, Solver.Node<width>, key, graph)), Solver.generate(remaining, width, graph)) ==
     Lemmas.outcomes(Solver.forest(remaining, width, Solver.children(width, Finite.get(width, Solver.Node<width>, key, graph)), graph)) : List<&2, Game.Outcome>}) ->
  {Finite.get(width, Game.Outcome, key, Solver.generate(1n+remaining, width, graph)) ==
   Game.evaluate(Solver.assemble(width, Finite.get(width, Solver.Node<width>, key, graph),
     Solver.forest(remaining, width, Solver.children(width, Finite.get(width, Solver.Node<width>, key, graph)), graph))) : Game.Outcome}:
  +node = Finite.get(width, Solver.Node<width>, key, graph)
  +trees = Solver.forest(remaining, width, Solver.children(width, node), graph)
  +values = Solver.values(width, Solver.children(width, node), Solver.generate(remaining, width, graph))
  Equal.trans(Game.Outcome,
    Finite.get(width, Game.Outcome, key, Solver.generate(1n+remaining, width, graph)),
    Solver.combine(width, node, values), Game.evaluate(Solver.assemble(width, node, trees)),
    lookup(width, graph, Solver.Next{Solver.generate(remaining, width, graph)}, key),
    Equal.trans(Game.Outcome, Solver.combine(width, node, values), Solver.combine(width, node, Lemmas.outcomes(trees)),
      Game.evaluate(Solver.assemble(width, node, trees)),
      Equal.cong(List<&2, Game.Outcome>, Game.Outcome, outcomes => Solver.combine(width, node, outcomes),
        values, Lemmas.outcomes(trees), children), assemble_evaluate(width, node, trees)))

# Clock/list induction, with width and all keys symbolic. Resets use the
# completed dependency value even at clock zero; only Quiet consumes clock.
def forest_correct(remaining: Nat, +width: Nat, +edges: List<&2, Solver.Edge<width>>,
  +graph: Finite.Table(width, Solver.Node<width>)) ->
  {Solver.values(width, edges, Solver.generate(remaining, width, graph)) ==
   Lemmas.outcomes(Solver.forest(remaining, width, edges, graph)) : List<&2, Game.Outcome>}:
  match remaining edges:
    case 0n Nil{}:
      {==}
    case 1n+rest Nil{}:
      {==}
    case 0n Solver.Reset{result} <> tail:
      Lemmas.cons_cong(Game.Outcome, result, result,
        Solver.values(width, tail, Solver.generate(0n, width, graph)), Lemmas.outcomes(Solver.forest(0n, width, tail, graph)),
        {==}, forest_correct(0n, width, tail, graph))
    case 1n++rest Solver.Reset{result} <> tail:
      Lemmas.cons_cong(Game.Outcome, result, result,
        Solver.values(width, tail, Solver.generate(1n+rest, width, graph)), Lemmas.outcomes(Solver.forest(1n+rest, width, tail, graph)),
        {==}, forest_correct(1n+rest, width, tail, graph))
    case 0n Solver.Quiet{key} <> tail:
      Lemmas.cons_cong(Game.Outcome,
        Finite.get(width, Game.Outcome, key, Solver.generate(0n, width, graph)),
        Solver.boundary(width, Finite.get(width, Solver.Node<width>, key, graph)),
        Solver.values(width, tail, Solver.generate(0n, width, graph)), Lemmas.outcomes(Solver.forest(0n, width, tail, graph)),
        lookup(width, graph, Solver.Initial{}, key), forest_correct(0n, width, tail, graph))
    case 1n++rest Solver.Quiet{key} <> tail:
      +node = Finite.get(width, Solver.Node<width>, key, graph)
      Lemmas.cons_cong(Game.Outcome,
        Finite.get(width, Game.Outcome, key, Solver.generate(1n+rest, width, graph)),
        Game.evaluate(Solver.assemble(width, node, Solver.forest(rest, width, Solver.children(width, node), graph))),
        Solver.values(width, tail, Solver.generate(1n+rest, width, graph)), Lemmas.outcomes(Solver.forest(1n+rest, width, tail, graph)),
        step(rest, width, graph, key, forest_correct(rest, width, Solver.children(width, node), graph)),
        forest_correct(1n+rest, width, tail, graph))

def pointwise(+remaining: Nat, +width: Nat, +graph: Finite.Table(width, Solver.Node<width>), +key: Word(width)) ->
  {Finite.get(width, Game.Outcome, key, Solver.generate(remaining, width, graph)) ==
   Game.evaluate(Solver.tree(remaining, width, graph, key)) : Game.Outcome}:
  +trees = Solver.forest(remaining, width, Solver.Quiet{key} <> Nil{}, graph)
  %Lemmas.first_outcomes(trees) :
    {Finite.get(width, Game.Outcome, key, Solver.generate(remaining, width, graph)) == _ : Game.Outcome}
  Equal.cong(List<&2, Game.Outcome>, Game.Outcome, xs => Lemmas.first(xs),
    Solver.values(width, Solver.Quiet{key} <> Nil{}, Solver.generate(remaining, width, graph)), Lemmas.outcomes(trees),
    forest_correct(remaining, width, Solver.Quiet{key} <> Nil{}, graph))

def serialized_value(+remaining: Nat, +width: Nat, +graph: Finite.Table(width, Solver.Node<width>), +key: Word(width)) ->
  {Finite.read(Solver.file(remaining, width, graph), Finite.offset(width, key)) ==
   Some{Game.byte(Game.evaluate(Solver.tree(remaining, width, graph, key)))} : Maybe<&2, U32>}:
  +table = Solver.generate(remaining, width, graph)
  +stored = Finite.get(width, U32, key, Engine.bytes(width, table))
  +value = Finite.get(width, Game.Outcome, key, table)
  +expected = Game.evaluate(Solver.tree(remaining, width, graph, key))
  Equal.trans(Maybe<&2, U32>, Finite.read(Solver.file(remaining, width, graph), Finite.offset(width, key)),
    Some{stored}, Some{Game.byte(expected)}, FiniteProof.read_go(width, Engine.bytes(width, table), key, Nil{}),
    Equal.trans(Maybe<&2, U32>, Some{stored}, Some{Game.byte(value)}, Some{Game.byte(expected)},
      Equal.cong(U32, Maybe<&2, U32>, byte => Some{byte}, stored, Game.byte(value), EngineProof.bytes_get(width, table, key)),
      Equal.cong(Game.Outcome, Maybe<&2, U32>, outcome => Some{Game.byte(outcome)}, value, expected,
        pointwise(remaining, width, graph, key))))

def file_length(+remaining: Nat, +width: Nat, +graph: Finite.Table(width, Solver.Node<width>)) ->
  {List.length(&2, U32, Solver.file(remaining, width, graph)) == Finite.size(width) : Nat}:
  Equal.trans(Nat, List.length(&2, U32, Solver.file(remaining, width, graph)), Nat.add(Finite.size(width), 0n), Finite.size(width),
    FiniteProof.length_go(width, Engine.bytes(width, Solver.generate(remaining, width, graph)), Nil{}),
    Lemmas.add_zero(Finite.size(width)))
