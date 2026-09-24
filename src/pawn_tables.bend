import Base
import ./material_cache.bend as Registry
import ./table_cache.bend as Cache
import ./game.bend as Game
import ./pawnless_chess.bend as Chess
import ./pawn_chess.bend as Pawn
import ./pawnless_index.bend as Index
import ./finite_table.bend as Finite
import ./table_engine.bend as Engine
import ./clock_solver.bend as Solver
import ./pawnless_tables.bend as Pawnless
import ./dependency_engine.bend as Dependencies
import ./material_catalog.bend as Catalog

# Every rank is solved at all clocks before the next rank starts. A pawn push
# consults an already completed rank at clock zero (limit halfmoves left).
def PromotionContext(width: Nat) -> Data:
  Nat

def promotion_entry(+width: Nat, limit: Nat, kind: Chess.Material) -> Cache.Entry:
  Cache.Entry{width, Pawnless.generate(limit, width, kind)}

def promotions(limit: Nat, +width: Nat) -> List<&2, Registry.Named>:
  Catalog.named(Dependencies.family(~Chess.Material, ~PromotionContext, ~Cache.Family, ~promotion_entry, 2n, width, limit, Catalog.pieces()))

def draws(depth: Nat) -> Finite.Table(depth, Game.Outcome):
  match depth:
    case 0n:
      Game.Draw{}
    case 1n++rest:
      +tail = draws(rest)
      Finite.Fork{tail, tail}

type Sources<-width: Nat> is Data:
  Sources{quiet: Finite.Table(width, Game.Outcome), push: Cache.Entry,
    double: Cache.Entry, promotions: List<&2, Registry.Named>}

def lookup(+width: Nat, advance: Nat, position: Pawn.Position,
  table: Finite.Table(width, Game.Outcome)) -> Game.Outcome:
  Finite.get(width, Game.Outcome, Index.encode_at(width, Pawn.board(advance, position)), table)

def dependency(+width: Nat, advance: Nat, position: Pawn.Position, entry: Cache.Entry) -> Game.Outcome:
  Cache.value(Cache.lookup(width, Index.encode_at(width, Pawn.board(advance, position)), entry), Game.Draw{})

def double_value(prior: Nat, position: Pawn.Position, +width: Nat,
  table: Cache.Entry) -> Game.Outcome:
  match prior:
    case 0n:
      Game.Draw{}
    case 1n+rest:
      dependency(width, rest, position, table)

def compile_edge(advance: Nat, +width: Nat, push: Cache.Entry,
  double: Cache.Entry, promotions: List<&2, Registry.Named>, edge: Pawn.Edge) -> Solver.Edge<width>:
  match advance edge:
    case 1n+prior Pawn.Quiet{position}:
      Solver.Quiet{Index.encode_at(width, Pawn.board(1n+prior, position))}
    case 1n+prior Pawn.Push{position}:
      Solver.Reset{dependency(width, prior, position, push)}
    case 1n+prior Pawn.DoublePush{position}:
      Solver.Reset{double_value(prior, position, width, double)}
    case 1n+prior Pawn.Promoted{material, board}:
      Solver.Reset{Cache.value(Registry.lookup(promotions, Catalog.signature(material), width, Index.encode_at(width, board)), Game.Draw{})}
    case _ _:
      Solver.Reset{Game.Draw{}}

def edge_value(advance: Nat, edge: Pawn.Edge, +width: Nat, sources: Sources<width>) -> Game.Outcome:
  match sources:
    case Sources{quiet, push, double, promotions}:
      Solver.edge_value(width, compile_edge(advance, width, push, double, promotions, edge), quiet)

def values(items: List<&2, Pawn.Task>, +advance: Nat, +width: Nat, +sources: Sources<width>) -> List<&2, Game.Outcome>:
  match items:
    case Nil{}:
      Nil{}
    case Pawn.Follow{edge} <> tail:
      edge_value(advance, edge, width, sources) <> values(tail, advance, width, sources)
    case Pawn.Here{position} <> tail:
      Game.Draw{} <> values(tail, advance, width, sources)

def combine(view: Pawn.View, outcomes: List<&2, Game.Outcome>) -> Game.Outcome:
  match view outcomes:
    case Pawn.Stop{outcome} _:
      outcome
    case Pawn.Play{turn, edges} Nil{}:
      Game.Draw{}
    case Pawn.Play{turn, edges} head <> tail:
      Engine.fold(tail, turn, head)

type Layer<-width: Nat> is Data:
  Boundary{advance: Nat}
  Step{advance: Nat, sources: Sources<width>}

def at(+width: Nat, layer: Layer<width>, position: Pawn.Position) -> Game.Outcome:
  match layer:
    case Boundary{0n}:
      Game.Draw{}
    case Boundary{1n+prior}:
      Game.evaluate(Pawn.boundary(Pawn.view(1n+prior, position)))
    case Step{0n, sources}:
      Game.Draw{}
    case Step{1n++prior, sources}:
      +node = Pawn.view(1n+prior, position)
      combine(node, values(Pawn.tasks(node), 1n+prior, width, sources))

def edges(items: List<&2, Pawn.Task>, +advance: Nat, +width: Nat, +push: Cache.Entry,
  +double: Cache.Entry, +promotions: List<&2, Registry.Named>) -> List<&2, Solver.Edge<width>>:
  match items:
    case Nil{}:
      Nil{}
    case Pawn.Here{position} <> tail:
      Solver.Reset{Game.Draw{}} <> edges(tail, advance, width, push, double, promotions)
    case Pawn.Follow{edge} <> tail:
      compile_edge(advance, width, push, double, promotions, edge) <> edges(tail, advance, width, push, double, promotions)

def node(+advance: Nat, +width: Nat, push: Cache.Entry,
  double: Cache.Entry, promotions: List<&2, Registry.Named>, +view: Pawn.View) -> Solver.Node<width>:
  match advance view:
    case 0n _:
      Solver.Terminal{Game.Draw{}}
    case 1n+prior Pawn.Stop{result}:
      Solver.Terminal{result}
    case 1n+prior Pawn.Play{turn, children}:
      Solver.Choice{turn, edges(Pawn.tasks(view), advance, width, push, double, promotions)}

def graph_fill(depth: Nat, +width: Nat, +advance: Nat, +push: Cache.Entry,
  +double: Cache.Entry, +promotions: List<&2, Registry.Named>,
  keys: Finite.Table(depth, Word(width))) -> Finite.Table(depth, Solver.Node<width>):
  match depth keys:
    case 0n key:
      node(advance, width, push, double, promotions, Pawn.view(advance, Pawn.position(Index.decode_at(width, key))))
    case 1n++rest Finite.Fork{left, right}:
      a b = graph_fill(rest, width, advance, push, double, promotions, left) graph_fill(rest, width, advance, push, double, promotions, right)
      Finite.Fork{a, b}

def graph(+width: Nat, advance: Nat, push: Cache.Entry,
  double: Cache.Entry, promotions: List<&2, Registry.Named>) -> Finite.Table(width, Solver.Node<width>):
  graph_fill(width, width, advance, push, double, promotions, Finite.keys(width))

def clock(remaining: Nat, advance: Nat, +width: Nat,
  +lower: List<&2, Cache.Entry>, promotions: List<&2, Registry.Named>) -> Finite.Table(width, Game.Outcome):
  Solver.generate(remaining, width, graph(width, advance,
    Dependencies.get(0n, Cache.Entry, Cache.Entry{width, draws(width)}, lower),
    Dependencies.get(0n, Cache.Entry, Cache.Entry{width, draws(width)}, Dependencies.tail(Cache.Entry, lower)), promotions))

# A proof projection, not another clock evaluator.
def layer_phase(+width: Nat, advance: Nat, push: Cache.Entry,
  double: Cache.Entry, promotions: List<&2, Registry.Named>, phase: Solver.Layer<width>) -> Layer<width>:
  match phase:
    case Solver.Initial{}:
      Boundary{advance}
    case Solver.Next{previous}:
      Step{advance, Sources{previous, push, double, promotions}}

def phase(remaining: Nat, +advance: Nat, +width: Nat, +lower: List<&2, Cache.Entry>,
  +promotions: List<&2, Registry.Named>) -> Layer<width>:
  match remaining:
    case 0n:
      Boundary{advance}
    case 1n+rest:
      Step{advance, Sources{clock(rest, advance, width, lower, promotions),
        Dependencies.get(0n, Cache.Entry, Cache.Entry{width, draws(width)}, lower),
        Dependencies.get(0n, Cache.Entry, Cache.Entry{width, draws(width)}, Dependencies.tail(Cache.Entry, lower)), promotions}}

type ScheduleContext is Data:
  ScheduleContext{limit: Nat, promotions: List<&2, Registry.Named>}

def Schedule(width: Nat) -> Data:
  ScheduleContext

def component(+stage: Nat, +width: Nat, context: Schedule(width), lower: List<&2, Cache.Entry>) -> Cache.Entry:
  match context:
    case ScheduleContext{limit, promotions}:
      Cache.Entry{width, clock(limit, stage, width, lower, promotions)}

def history(advance: Nat, +width: Nat, limit: Nat, promotions: List<&2, Registry.Named>) -> List<&2, Cache.Entry>:
  Dependencies.history(~Schedule, ~Cache.Family, ~component, advance, width, ScheduleContext{limit, promotions})

# This projection exposes arbitrary clocks for the proof. The file generator
# below builds history once and shares its completed tables across all slots.
def solve(advance: Nat, remaining: Nat, +width: Nat, +limit: Nat,
  +promotions: List<&2, Registry.Named>) -> Finite.Table(width, Game.Outcome):
  match advance:
    case 0n:
      draws(width)
    case 1n++prior:
      clock(remaining, 1n+prior, width, history(prior, width, limit, promotions), promotions)

def stored(advance: Nat, +width: Nat, ranks: List<&2, Cache.Entry>, key: Word(width)) -> Game.Outcome:
  match advance:
    case 0n:
      Game.Draw{}
    case 1n+prior:
      Cache.value(Cache.lookup(width, key,
        Dependencies.get(Nat.sub(5n, prior), Cache.Entry, Cache.Entry{width, draws(width)}, ranks)), Game.Draw{})

def RankContext(width: Nat, low: Nat) -> Data:
  List<&2, Cache.Entry>

def stored_entry(+width: Nat, +low: Nat, ranks: List<&2, Cache.Entry>, key: Word(width)) -> Game.Outcome:
  +word = key
  stored(Pawn.advance(Index.decode_at(width, word)), width, ranks, word)

def finish(depth: Nat, width: Nat, ranks: List<&2, Cache.Entry>,
  keys: Finite.Table(depth, Word(width))) -> Finite.Table(depth, Game.Outcome):
  Engine.fill(~RankContext, ~stored_entry, depth, width, 0n, ranks, keys)

def generate(+limit: Nat, +width: Nat) -> Finite.Table(width, Game.Outcome):
  finish(width, width, history(6n, width, limit, promotions(limit, width)), Finite.keys(width))

def file(limit: Nat, +width: Nat) -> List<&2, U32>:
  Finite.flatten(width, Engine.bytes(width, generate(limit, width)))
