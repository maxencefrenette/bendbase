import Base
import ./game.bend as Game
import ./pawnless_chess.bend as Chess
import ./pawnless_index.bend as Index
import ./finite_table.bend as Finite

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
  match rest:
    case Nil{}:
      first
    case head <> tail:
      Game.best(turn, first, fold(tail, turn, head))

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

def initial(depth: Nat, +width: Nat, +material: Chess.Material,
  keys: Finite.Table(depth, Word(width))) -> Finite.Table(depth, Game.Outcome):
  match depth keys:
    case 0n key:
      base(width, material, key)
    case 1n++rest Finite.Fork{left, right}:
      a b = initial(rest, width, material, left) initial(rest, width, material, right)
      Finite.Fork{a, b}

def layer(depth: Nat, +width: Nat, +material: Chess.Material,
  +previous: Finite.Table(width, Game.Outcome),
  keys: Finite.Table(depth, Word(width))) -> Finite.Table(depth, Game.Outcome):
  match depth keys:
    case 0n key:
      step(width, material, previous, key)
    case 1n++rest Finite.Fork{left, right}:
      a b = layer(rest, width, material, previous, left) layer(rest, width, material, previous, right)
      Finite.Fork{a, b}

def generate(remaining: Nat, +width: Nat, +material: Chess.Material) -> Finite.Table(width, Game.Outcome):
  match remaining:
    case 0n:
      initial(width, width, material, Finite.keys(width))
    case 1n+rest:
      layer(width, width, material, generate(rest, width, material), Finite.keys(width))

def bytes(depth: Nat, table: Finite.Table(depth, Game.Outcome)) -> Finite.Table(depth, U32):
  match depth table:
    case 0n outcome:
      Game.byte(outcome)
    case 1n++rest Finite.Fork{left, right}:
      Finite.Fork{bytes(rest, left), bytes(rest, right)}

def file(remaining: Nat, +width: Nat, material: Chess.Material) -> List<&2, U32>:
  Finite.flatten(width, bytes(width, generate(remaining, width, material)))
