import Base
import ./game.bend as Game
import ./pawnless_chess.bend as Chess
import ./pawn_chess.bend as Pawn
import ./pawnless_index.bend as Index
import ./finite_table.bend as Finite
import ./table_engine.bend as Engine
import ./clock_solver.bend as Solver
import ./pawnless_tables.bend as Pawnless

# Every rank is solved at all clocks before the next rank starts. A pawn push
# consults an already completed rank at clock zero (limit halfmoves left).
type Promotions<-width: Nat> is Data:
  Promotions{queen: Finite.Table(width, Game.Outcome), rook: Finite.Table(width, Game.Outcome),
    bishop: Finite.Table(width, Game.Outcome), knight: Finite.Table(width, Game.Outcome)}

def promotions(+limit: Nat, +width: Nat) -> Promotions<width>:
  queen rook = Pawnless.generate(limit, width, Chess.Queen{}) Pawnless.generate(limit, width, Chess.Rook{})
  bishop knight = Pawnless.generate(limit, width, Chess.Bishop{}) Pawnless.generate(limit, width, Chess.Knight{})
  Promotions{queen, rook, bishop, knight}

def promoted(-width: Nat, material: Chess.Material, tables: Promotions<width>) -> Finite.Table(width, Game.Outcome):
  match material tables:
    case Chess.Queen{} Promotions{queen, rook, bishop, knight}:
      queen
    case Chess.Rook{} Promotions{queen, rook, bishop, knight}:
      rook
    case Chess.Bishop{} Promotions{queen, rook, bishop, knight}:
      bishop
    case Chess.Knight{} Promotions{queen, rook, bishop, knight}:
      knight

def draws(depth: Nat) -> Finite.Table(depth, Game.Outcome):
  match depth:
    case 0n:
      Game.Draw{}
    case 1n++rest:
      +tail = draws(rest)
      Finite.Fork{tail, tail}

type Ranks<-width: Nat> is Data:
  NoRanks{}
  Rank{table: Finite.Table(width, Game.Outcome), earlier: Ranks<width>}

def top(+width: Nat, ranks: Ranks<width>) -> Finite.Table(width, Game.Outcome):
  match ranks:
    case NoRanks{}:
      draws(width)
    case Rank{table, earlier}:
      table

def earlier(-width: Nat, ranks: Ranks<width>) -> Ranks<width>:
  match ranks:
    case NoRanks{}:
      NoRanks{}
    case Rank{table, earlier}:
      earlier

type Sources<-width: Nat> is Data:
  Sources{quiet: Finite.Table(width, Game.Outcome), push: Finite.Table(width, Game.Outcome),
    double: Finite.Table(width, Game.Outcome), promotions: Promotions<width>}

def lookup(+width: Nat, advance: Nat, position: Pawn.Position,
  table: Finite.Table(width, Game.Outcome)) -> Game.Outcome:
  Finite.get(width, Game.Outcome, Index.encode_at(width, Pawn.board(advance, position)), table)

def double_value(prior: Nat, position: Pawn.Position, +width: Nat,
  table: Finite.Table(width, Game.Outcome)) -> Game.Outcome:
  match prior:
    case 0n:
      Game.Draw{}
    case 1n+rest:
      lookup(width, rest, position, table)

def compile_edge(advance: Nat, +width: Nat, push: Finite.Table(width, Game.Outcome),
  double: Finite.Table(width, Game.Outcome), promotions: Promotions<width>, edge: Pawn.Edge) -> Solver.Edge<width>:
  match advance edge:
    case 1n+prior Pawn.Quiet{position}:
      Solver.Quiet{Index.encode_at(width, Pawn.board(1n+prior, position))}
    case 1n+prior Pawn.Push{position}:
      Solver.Reset{lookup(width, prior, position, push)}
    case 1n+prior Pawn.DoublePush{position}:
      Solver.Reset{double_value(prior, position, width, double)}
    case 1n+prior Pawn.Promoted{material, board}:
      Solver.Reset{Finite.get(width, Game.Outcome, Index.encode_at(width, board), promoted(width, material, promotions))}
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

def edges(items: List<&2, Pawn.Task>, +advance: Nat, +width: Nat, +push: Finite.Table(width, Game.Outcome),
  +double: Finite.Table(width, Game.Outcome), +promotions: Promotions<width>) -> List<&2, Solver.Edge<width>>:
  match items:
    case Nil{}:
      Nil{}
    case Pawn.Here{position} <> tail:
      Solver.Reset{Game.Draw{}} <> edges(tail, advance, width, push, double, promotions)
    case Pawn.Follow{edge} <> tail:
      compile_edge(advance, width, push, double, promotions, edge) <> edges(tail, advance, width, push, double, promotions)

def node(+advance: Nat, +width: Nat, push: Finite.Table(width, Game.Outcome),
  double: Finite.Table(width, Game.Outcome), promotions: Promotions<width>, +view: Pawn.View) -> Solver.Node<width>:
  match advance view:
    case 0n _:
      Solver.Terminal{Game.Draw{}}
    case 1n+prior Pawn.Stop{result}:
      Solver.Terminal{result}
    case 1n+prior Pawn.Play{turn, children}:
      Solver.Choice{turn, edges(Pawn.tasks(view), advance, width, push, double, promotions)}

def graph_fill(depth: Nat, +width: Nat, +advance: Nat, +push: Finite.Table(width, Game.Outcome),
  +double: Finite.Table(width, Game.Outcome), +promotions: Promotions<width>,
  keys: Finite.Table(depth, Word(width))) -> Finite.Table(depth, Solver.Node<width>):
  match depth keys:
    case 0n key:
      node(advance, width, push, double, promotions, Pawn.view(advance, Pawn.position(Index.decode_at(width, key))))
    case 1n++rest Finite.Fork{left, right}:
      a b = graph_fill(rest, width, advance, push, double, promotions, left) graph_fill(rest, width, advance, push, double, promotions, right)
      Finite.Fork{a, b}

def graph(+width: Nat, advance: Nat, push: Finite.Table(width, Game.Outcome),
  double: Finite.Table(width, Game.Outcome), promotions: Promotions<width>) -> Finite.Table(width, Solver.Node<width>):
  graph_fill(width, width, advance, push, double, promotions, Finite.keys(width))

def clock(remaining: Nat, advance: Nat, +width: Nat,
  +lower: Ranks<width>, promotions: Promotions<width>) -> Finite.Table(width, Game.Outcome):
  Solver.generate(remaining, width, graph(width, advance, top(width, lower), top(width, earlier(width, lower)), promotions))

# A proof projection, not another clock evaluator.
def layer_phase(+width: Nat, advance: Nat, push: Finite.Table(width, Game.Outcome),
  double: Finite.Table(width, Game.Outcome), promotions: Promotions<width>, phase: Solver.Layer<width>) -> Layer<width>:
  match phase:
    case Solver.Initial{}:
      Boundary{advance}
    case Solver.Next{previous}:
      Step{advance, Sources{previous, push, double, promotions}}

def phase(remaining: Nat, +advance: Nat, +width: Nat, +lower: Ranks<width>,
  +promotions: Promotions<width>) -> Layer<width>:
  match remaining:
    case 0n:
      Boundary{advance}
    case 1n+rest:
      Step{advance, Sources{clock(rest, advance, width, lower, promotions),
        top(width, lower), top(width, earlier(width, lower)), promotions}}

def history(advance: Nat, +width: Nat, +limit: Nat, +promotions: Promotions<width>) -> Ranks<width>:
  match advance:
    case 0n:
      NoRanks{}
    case 1n++prior:
      +lower = history(prior, width, limit, promotions)
      Rank{clock(limit, 1n+prior, width, lower, promotions), lower}

# This projection exposes arbitrary clocks for the proof. The file generator
# below builds history once and shares its completed tables across all slots.
def solve(advance: Nat, remaining: Nat, +width: Nat, +limit: Nat,
  +promotions: Promotions<width>) -> Finite.Table(width, Game.Outcome):
  match advance:
    case 0n:
      draws(width)
    case 1n++prior:
      clock(remaining, 1n+prior, width, history(prior, width, limit, promotions), promotions)

def select(offset: Nat, +width: Nat, ranks: Ranks<width>) -> Finite.Table(width, Game.Outcome):
  match offset ranks:
    case 0n ranks:
      top(width, ranks)
    case 1n+rest NoRanks{}:
      draws(width)
    case 1n+rest Rank{table, earlier}:
      select(rest, width, earlier)

def stored(advance: Nat, +width: Nat, ranks: Ranks<width>, key: Word(width)) -> Game.Outcome:
  match advance:
    case 0n:
      Game.Draw{}
    case 1n+prior:
      Finite.get(width, Game.Outcome, key, select(Nat.sub(5n, prior), width, ranks))

def RankContext(width: Nat, low: Nat) -> Data:
  Ranks<width>

def stored_entry(+width: Nat, +low: Nat, ranks: Ranks<width>, key: Word(width)) -> Game.Outcome:
  +word = key
  stored(Pawn.advance(Index.decode_at(width, word)), width, ranks, word)

def finish(depth: Nat, width: Nat, ranks: Ranks<width>,
  keys: Finite.Table(depth, Word(width))) -> Finite.Table(depth, Game.Outcome):
  Engine.fill(~RankContext, ~stored_entry, depth, width, 0n, ranks, keys)

def generate(+limit: Nat, +width: Nat) -> Finite.Table(width, Game.Outcome):
  finish(width, width, history(6n, width, limit, promotions(limit, width)), Finite.keys(width))

def file(limit: Nat, +width: Nat) -> List<&2, U32>:
  Finite.flatten(width, Engine.bytes(width, generate(limit, width)))
