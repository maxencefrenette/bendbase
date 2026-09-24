import Base
import ./game.bend as Game
import ./pawnless_chess.bend as Chess
import ./pawnless_index.bend as Index
import ./finite_table.bend as Finite
import ./table_engine.bend as Engine

def values(states: List<&2, Chess.State>, +width: Nat,
  +table: Finite.Table(width, Game.Outcome)) -> List<&2, Game.Outcome>:
  match states:
    case Nil{}:
      Nil{}
    case Chess.KingsOnly{} <> tail:
      Game.Draw{} <> values(tail, width, table)
    case Chess.Three{board} <> tail:
      Finite.get(width, Game.Outcome, Index.encode_at(width, board), table) <> values(tail, width, table)

def fold(rest: List<&2, Game.Outcome>, +turn: Game.Player, first: Game.Outcome) -> Game.Outcome:
  Engine.fold(rest, turn, first)

def combine(view: Chess.View, outcomes: List<&2, Game.Outcome>) -> Game.Outcome:
  match view outcomes:
    case Chess.Stop{outcome} _:
      outcome
    case Chess.Play{turn, children} Nil{}:
      Game.Draw{}
    case Chess.Play{turn, children} head <> tail:
      fold(tail, turn, head)

def base(+width: Nat, material: Chess.Material, key: Word(width)) -> Game.Outcome:
  Game.evaluate(Chess.boundary(Chess.view(material, Chess.Three{Index.decode_at(width, key)})))

def at(+width: Nat, material: Chess.Material, previous: Finite.Table(width, Game.Outcome), board: Chess.Board) -> Game.Outcome:
  +node = Chess.view(material, Chess.Three{board})
  combine(node, values(Chess.children(node), width, previous))

def step(+width: Nat, material: Chess.Material, previous: Finite.Table(width, Game.Outcome), key: Word(width)) -> Game.Outcome:
  at(width, material, previous, Index.decode_at(width, key))

# The adapter supplies chess-specific entries; traversal and clock iteration
# belong to Engine. These small projections are also used by the chess proof.
type Layer<-width: Nat> is Data:
  Initial{material: Chess.Material}
  Next{material: Chess.Material, previous: Finite.Table(width, Game.Outcome)}

def LayerContext(width: Nat, low: Nat) -> Data:
  Layer<width>

def entry(+width: Nat, +low: Nat, context: Layer<width>, key: Word(width)) -> Game.Outcome:
  match context:
    case Initial{material}:
      base(width, material, key)
    case Next{material, previous}:
      step(width, material, previous, key)

def initial(depth: Nat, width: Nat, material: Chess.Material,
  keys: Finite.Table(depth, Word(width))) -> Finite.Table(depth, Game.Outcome):
  Engine.fill(~LayerContext, ~entry, depth, width, 0n, Initial{material}, keys)

def layer(depth: Nat, width: Nat, material: Chess.Material,
  previous: Finite.Table(width, Game.Outcome),
  keys: Finite.Table(depth, Word(width))) -> Finite.Table(depth, Game.Outcome):
  Engine.fill(~LayerContext, ~entry, depth, width, 0n, Next{material, previous}, keys)

def Context(width: Nat, low: Nat) -> Data:
  Chess.Material

def boundary(+width: Nat, +low: Nat, material: Chess.Material) -> Finite.Table(width, Game.Outcome):
  initial(width, width, material, Finite.keys(width))

def sweep(+width: Nat, +low: Nat, material: Chess.Material,
  previous: Finite.Table(width, Game.Outcome)) -> Finite.Table(width, Game.Outcome):
  layer(width, width, material, previous, Finite.keys(width))

def generate(remaining: Nat, width: Nat, material: Chess.Material) -> Finite.Table(width, Game.Outcome):
  Engine.generate(~Context, ~boundary, ~sweep, remaining, width, 0n, material)

# Compatibility projections shared by the existing serialization proofs.
def bytes(depth: Nat, table: Finite.Table(depth, Game.Outcome)) -> Finite.Table(depth, U32):
  Engine.bytes(depth, table)

def file(remaining: Nat, +width: Nat, material: Chess.Material) -> List<&2, U32>:
  Finite.flatten(width, bytes(width, generate(remaining, width, material)))
