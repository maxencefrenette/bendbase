import Base
import ./table_cache.bend as Cache
import ./dependency_engine.bend as Dependencies
import ./game.bend as Game
import ./pawn_chess.bend as Pawn
import ./pawnless_index.bend as Index
import ./pawn_tables.bend as Tables
import ./pawnless_tables_proof.bend as Lemmas
import ./finite_table.bend as Finite
import ./finite_table_proof.bend as FiniteProof
import ./clock_solver.bend as Solver
import ./clock_solver_proof.bend as SolverProof

def graph_get(depth: Nat, +width: Nat, +advance: Nat, +push: Cache.Entry,
  +double: Cache.Entry, +promotions: Finite.Table(2n, Cache.Entry),
  +keys: Finite.Table(depth, Word(width)), +key: Word(depth)) ->
  {Finite.get(depth, Solver.Node<width>, key, Tables.graph_fill(depth, width, advance, push, double, promotions, keys)) ==
   Tables.node(advance, width, push, double, promotions,
     Pawn.view(advance, Pawn.position(Index.decode_at(width, Finite.get(depth, Word(width), key, keys))))) : Solver.Node<width>}:
  match depth keys key:
    case 0n word WNil{}:
      {==}
    case 1n+rest Finite.Fork{left, right} WCon{False{}, tail}:
      graph_get(rest, width, advance, push, double, promotions, left, tail)
    case 1n+rest Finite.Fork{left, right} WCon{True{}, tail}:
      graph_get(rest, width, advance, push, double, promotions, right, tail)

def graph_lookup(+width: Nat, +advance: Nat, +push: Cache.Entry,
  +double: Cache.Entry, +promotions: Finite.Table(2n, Cache.Entry), +key: Word(width)) ->
  {Finite.get(width, Solver.Node<width>, key, Tables.graph(width, advance, push, double, promotions)) ==
   Tables.node(advance, width, push, double, promotions, Pawn.view(advance, Pawn.position(Index.decode_at(width, key)))) : Solver.Node<width>}:
  %FiniteProof.keys_get(width, key) :
    {Finite.get(width, Solver.Node<width>, key, Tables.graph(width, advance, push, double, promotions)) ==
     Tables.node(advance, width, push, double, promotions, Pawn.view(advance, Pawn.position(Index.decode_at(width, _)))) : Solver.Node<width>}
  graph_get(width, width, advance, push, double, promotions, Finite.keys(width), key)

def edge_values(items: List<&2, Pawn.Task>, +advance: Nat, +width: Nat, +previous: Finite.Table(width, Game.Outcome),
  +push: Cache.Entry, +double: Cache.Entry, +promotions: Finite.Table(2n, Cache.Entry)) ->
  {Solver.values(width, Tables.edges(items, advance, width, push, double, promotions), previous) ==
   Tables.values(items, advance, width, Tables.Sources{previous, push, double, promotions}) : List<&2, Game.Outcome>}:
  match items:
    case Nil{}:
      {==}
    case Pawn.Here{position} <> +tail:
      Lemmas.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        Solver.values(width, Tables.edges(tail, advance, width, push, double, promotions), previous),
        Tables.values(tail, advance, width, Tables.Sources{previous, push, double, promotions}),
        {==}, edge_values(tail, advance, width, previous, push, double, promotions))
    case Pawn.Follow{edge} <> +tail:
      +value = Tables.edge_value(advance, edge, width, Tables.Sources{previous, push, double, promotions})
      Lemmas.cons_cong(Game.Outcome, value, value,
        Solver.values(width, Tables.edges(tail, advance, width, push, double, promotions), previous),
        Tables.values(tail, advance, width, Tables.Sources{previous, push, double, promotions}),
        {==}, edge_values(tail, advance, width, previous, push, double, promotions))

def compiled_combine(+advance: Nat, +width: Nat, +push: Cache.Entry,
  +double: Cache.Entry, +promotions: Finite.Table(2n, Cache.Entry),
  +view: Pawn.View, +values: List<&2, Game.Outcome>) ->
  {Solver.combine(width, Tables.node(1n+advance, width, push, double, promotions, view), values) == Tables.combine(view, values) : Game.Outcome}:
  match view values:
    case Pawn.Stop{result} _:
      {==}
    case Pawn.Play{turn, children} Nil{}:
      {==}
    case Pawn.Play{turn, children} head <> tail:
      {==}

def compiled_boundary(+advance: Nat, +width: Nat, +push: Cache.Entry,
  +double: Cache.Entry, +promotions: Finite.Table(2n, Cache.Entry), +view: Pawn.View) ->
  {Solver.boundary(width, Tables.node(1n+advance, width, push, double, promotions, view)) == Game.evaluate(Pawn.boundary(view)) : Game.Outcome}:
  match view:
    case Pawn.Stop{result}:
      {==}
    case Pawn.Play{turn, children}:
      {==}

def compiled_step(+advance: Nat, +width: Nat, +previous: Finite.Table(width, Game.Outcome),
  +push: Cache.Entry, +double: Cache.Entry,
  +promotions: Finite.Table(2n, Cache.Entry), +view: Pawn.View) ->
  {Solver.at(width, Solver.Next{previous}, Tables.node(1n+advance, width, push, double, promotions, view)) ==
   Tables.combine(view, Tables.values(Pawn.tasks(view), 1n+advance, width, Tables.Sources{previous, push, double, promotions})) : Game.Outcome}:
  match view:
    case Pawn.Stop{result}:
      {==}
    case Pawn.Play{turn, children}:
      +values = Tables.values(Pawn.tasks(view), 1n+advance, width, Tables.Sources{previous, push, double, promotions})
      Equal.trans(Game.Outcome,
        Solver.at(width, Solver.Next{previous}, Tables.node(1n+advance, width, push, double, promotions, view)),
        Solver.combine(width, Tables.node(1n+advance, width, push, double, promotions, view), values), Tables.combine(view, values),
        Equal.cong(List<&2, Game.Outcome>, Game.Outcome, xs => Solver.combine(width, Tables.node(1n+advance, width, push, double, promotions, view), xs),
          Solver.values(width, Tables.edges(Pawn.tasks(view), 1n+advance, width, push, double, promotions), previous), values,
          edge_values(Pawn.tasks(view), 1n+advance, width, previous, push, double, promotions)),
        compiled_combine(advance, width, push, double, promotions, view, values))

def compiled_at(+advance: Nat, +width: Nat, +push: Cache.Entry,
  +double: Cache.Entry, +promotions: Finite.Table(2n, Cache.Entry),
  +phase: Solver.Layer<width>, +position: Pawn.Position) ->
  {Solver.at(width, phase, Tables.node(advance, width, push, double, promotions, Pawn.view(advance, position))) ==
   Tables.at(width, Tables.layer_phase(width, advance, push, double, promotions, phase), position) : Game.Outcome}:
  match advance phase:
    case 0n Solver.Initial{}:
      {==}
    case 0n Solver.Next{previous}:
      {==}
    case 1n+prior Solver.Initial{}:
      compiled_boundary(prior, width, push, double, promotions, Pawn.view(1n+prior, position))
    case 1n+prior Solver.Next{previous}:
      compiled_step(prior, width, previous, push, double, promotions, Pawn.view(1n+prior, position))

def layer_lookup(+width: Nat, +advance: Nat, +push: Cache.Entry,
  +double: Cache.Entry, +promotions: Finite.Table(2n, Cache.Entry), +phase: Solver.Layer<width>, +key: Word(width)) ->
  {Finite.get(width, Game.Outcome, key, Solver.layer(width, Tables.graph(width, advance, push, double, promotions), phase)) ==
   Tables.at(width, Tables.layer_phase(width, advance, push, double, promotions, phase), Pawn.position(Index.decode_at(width, key))) : Game.Outcome}:
  +graph = Tables.graph(width, advance, push, double, promotions)
  +position = Pawn.position(Index.decode_at(width, key))
  +node = Tables.node(advance, width, push, double, promotions, Pawn.view(advance, position))
  Equal.trans(Game.Outcome,
    Finite.get(width, Game.Outcome, key, Solver.layer(width, graph, phase)), Solver.at(width, phase, node),
    Tables.at(width, Tables.layer_phase(width, advance, push, double, promotions, phase), position),
    Equal.trans(Game.Outcome,
      Finite.get(width, Game.Outcome, key, Solver.layer(width, graph, phase)),
      Solver.at(width, phase, Finite.get(width, Solver.Node<width>, key, graph)), Solver.at(width, phase, node),
      SolverProof.lookup(width, graph, phase, key),
      Equal.cong(Solver.Node<width>, Game.Outcome, n => Solver.at(width, phase, n),
        Finite.get(width, Solver.Node<width>, key, graph), node, graph_lookup(width, advance, push, double, promotions, key))),
    compiled_at(advance, width, push, double, promotions, phase, position))

def clock_get(+remaining: Nat, +advance: Nat, +width: Nat, +lower: List<&2, Cache.Entry>,
  +promotions: Finite.Table(2n, Cache.Entry), +key: Word(width)) ->
  {Finite.get(width, Game.Outcome, key, Tables.clock(remaining, advance, width, lower, promotions)) ==
   Tables.at(width, Tables.phase(remaining, advance, width, lower, promotions), Pawn.position(Index.decode_at(width, key))) : Game.Outcome}:
  match remaining:
    case 0n:
      layer_lookup(width, advance, Dependencies.get(0n, Cache.Entry, Cache.Entry{width, Tables.draws(width)}, lower), Dependencies.get(0n, Cache.Entry, Cache.Entry{width, Tables.draws(width)}, Dependencies.tail(Cache.Entry, lower)), promotions, Solver.Initial{}, key)
    case 1n+rest:
      layer_lookup(width, advance, Dependencies.get(0n, Cache.Entry, Cache.Entry{width, Tables.draws(width)}, lower), Dependencies.get(0n, Cache.Entry, Cache.Entry{width, Tables.draws(width)}, Dependencies.tail(Cache.Entry, lower)), promotions,
        Solver.Next{Tables.clock(rest, advance, width, lower, promotions)}, key)
