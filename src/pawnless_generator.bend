import Base
import ./game.bend as Game
import ./pawnless_chess.bend as Three
import ./pawnless_index.bend as Index
import ./four_index.bend as FourIndex
import ./material_chess.bend as Chess
import ./four_chess.bend as Rules
import ./finite_table.bend as Finite
import ./table_engine.bend as Engine

# Clock-layer dynamic programming over the SAME generalized move rules as
# the chess semantics. No recursive game evaluation occurs in a layer.
type Scope is Data:
  Single{kind: Three.Material}
  Double{material: FourIndex.Material}

type Bundle<-width: Nat> is Data:
  Bundle{queen: Finite.Table(width, Game.Outcome), rook: Finite.Table(width, Game.Outcome),
    bishop: Finite.Table(width, Game.Outcome), knight: Finite.Table(width, Game.Outcome)}

def select(-width: Nat, kind: Three.Material, bundle: Bundle<width>) -> Finite.Table(width, Game.Outcome):
  match kind bundle:
    case Three.Queen{} Bundle{q, r, b, n}:
      q
    case Three.Rook{} Bundle{q, r, b, n}:
      r
    case Three.Bishop{} Bundle{q, r, b, n}:
      b
    case Three.Knight{} Bundle{q, r, b, n}:
      n

def decode(+width: Nat, scope: Scope, key: Word(width)) -> Chess.Position:
  match scope:
    case Single{kind}:
      Chess.from_three(kind, Index.decode_at(width, key))
    case Double{material}:
      FourIndex.position(material, FourIndex.decode_at(width, key))

def lower_value(+width: Nat, lower: Maybe<&2, Bundle<width>>, kind: Three.Material, board: Three.Board) -> Game.Outcome:
  match lower:
    case None{}:
      Game.Draw{}
    case Some{bundle}:
      Finite.get(width, Game.Outcome, Index.encode_at(width, board), select(width, kind, bundle))

def lookup(+width: Nat, +low: Nat, scope: Scope, previous: Finite.Table(width, Game.Outcome),
  lower: Maybe<&2, Bundle<low>>, position: Chess.Position) -> Game.Outcome:
  match scope position:
    case Single{kind} Chess.Position{turn, wk, bk, Chess.Man{owner, actual, pc} <> Nil{}}:
      Finite.get(width, Game.Outcome, Index.encode_at(width, Three.Board{owner, turn, wk, bk, pc}), previous)
    case Double{material} Chess.Position{turn, wk, bk, Chess.Man{owner, kind, pc} <> Nil{}}:
      lower_value(low, lower, kind, Three.Board{owner, turn, wk, bk, pc})
    case Double{material} Chess.Position{turn, wk, bk, Chess.Man{owner, first, pc} <> Chess.Man{other, second, at} <> Nil{}}:
      Finite.get(width, Game.Outcome, FourIndex.encode_at(width, FourIndex.Board{Three.Board{owner, turn, wk, bk, pc}, at}), previous)
    case _ _:
      Game.Draw{}

def values(positions: List<&2, Chess.Position>, +width: Nat, +low: Nat, +scope: Scope,
  +previous: Finite.Table(width, Game.Outcome), +lower: Maybe<&2, Bundle<low>>) -> List<&2, Game.Outcome>:
  match positions:
    case Nil{}:
      Nil{}
    case head <> tail:
      lookup(width, low, scope, previous, lower, head) <> values(tail, width, low, scope, previous, lower)

type Layer<-width: Nat> is Data:
  Initial{}
  Next{previous: Finite.Table(width, Game.Outcome)}

def combine(view: Rules.View, values: List<&2, Game.Outcome>) -> Game.Outcome:
  match view values:
    case Rules.Stop{result} _:
      result
    case Rules.Play{turn, children} Nil{}:
      Game.Draw{}
    case Rules.Play{turn, children} head <> tail:
      Engine.fold(tail, turn, head)

def at(+width: Nat, +low: Nat, +scope: Scope, layer: Layer<width>, lower: Maybe<&2, Bundle<low>>,
  moves: Nat, position: Chess.Position) -> Game.Outcome:
  match layer:
    case Initial{}:
      Game.evaluate(Rules.boundary(Rules.view(moves, position)))
    case Next{previous}:
      +node = Rules.view(moves, position)
      combine(node, values(Rules.children(node), width, low, scope, previous, lower))

type Config<-low: Nat> is Data:
  Config{scope: Scope, lower: Maybe<&2, Bundle<low>>, moves: Nat}

type EntryContext<-width: Nat, -low: Nat> is Data:
  EntryContext{config: Config<low>, layer: Layer<width>}

def LayerContext(width: Nat, low: Nat) -> Data:
  EntryContext<width, low>

def entry(+width: Nat, +low: Nat, context: EntryContext<width, low>, key: Word(width)) -> Game.Outcome:
  match context:
    case EntryContext{Config{+scope, lower, moves}, layer}:
      at(width, low, scope, layer, lower, moves, decode(width, scope, key))

def fill(depth: Nat, width: Nat, low: Nat, scope: Scope, layer: Layer<width>,
  lower: Maybe<&2, Bundle<low>>, moves: Nat, keys: Finite.Table(depth, Word(width))) -> Finite.Table(depth, Game.Outcome):
  Engine.fill(~LayerContext, ~entry, depth, width, low, EntryContext{Config{scope, lower, moves}, layer}, keys)

def Context(width: Nat, low: Nat) -> Data:
  Config<low>

def boundary(+width: Nat, +low: Nat, config: Config<low>) -> Finite.Table(width, Game.Outcome):
  Engine.fill(~LayerContext, ~entry, width, width, low, EntryContext{config, Initial{}}, Finite.keys(width))

def sweep(+width: Nat, +low: Nat, config: Config<low>,
  previous: Finite.Table(width, Game.Outcome)) -> Finite.Table(width, Game.Outcome):
  Engine.fill(~LayerContext, ~entry, width, width, low, EntryContext{config, Next{previous}}, Finite.keys(width))

# Captures consult immutable lower-material dependencies, not the previous
# four-man clock layer. The shared engine owns the reversible-clock iteration.
def generate(remaining: Nat, width: Nat, low: Nat, scope: Scope, moves: Nat,
  lower: Maybe<&2, Bundle<low>>) -> Finite.Table(width, Game.Outcome):
  Engine.generate(~Context, ~boundary, ~sweep, remaining, width, low, Config{scope, lower, moves})

def phase(remaining: Nat, +width: Nat, +low: Nat, +scope: Scope, +moves: Nat,
  +lower: Maybe<&2, Bundle<low>>) -> Layer<width>:
  match remaining:
    case 0n:
      Initial{}
    case 1n+rest:
      Next{generate(rest, width, low, scope, moves, lower)}

def singles(+limit: Nat, +width: Nat, +moves: Nat) -> Bundle<width>:
  q r = generate(limit, width, width, Single{Three.Queen{}}, moves, None{}) generate(limit, width, width, Single{Three.Rook{}}, moves, None{})
  b n = generate(limit, width, width, Single{Three.Bishop{}}, moves, None{}) generate(limit, width, width, Single{Three.Knight{}}, moves, None{})
  Bundle{q, r, b, n}

def four(+limit: Nat, width: Nat, +low: Nat, +moves: Nat, material: FourIndex.Material) -> Finite.Table(width, Game.Outcome):
  generate(limit, width, low, Double{material}, moves, Some{singles(limit, low, moves)})

def file_with(limit: Nat, +width: Nat, low: Nat, moves: Nat, material: FourIndex.Material, lower: Bundle<low>) -> List<&2, U32>:
  Finite.flatten(width, Engine.bytes(width, generate(limit, width, low, Double{material}, moves, Some{lower})))

def file(+limit: Nat, +width: Nat, +low: Nat, +moves: Nat, material: FourIndex.Material) -> List<&2, U32>:
  file_with(limit, width, low, moves, material, singles(limit, low, moves))
