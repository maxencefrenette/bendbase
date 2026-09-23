import Base
import ./game.bend as Game
import ./pawnless_chess.bend as Three
import ./material_chess.bend as Chess
import ./four_chess.bend as Rules
import ./pawnless_tables.bend as Pawnless

# Reference minimax recurrence for the proof-only milestone. It folds outcomes
# directly, without constructing Game.Tree or calling its evaluator recursively.
# It is deliberately not a memoized/table-speed implementation.
def first(values: List<&2, Game.Outcome>) -> Game.Outcome:
  match values:
    case Nil{}:
      Game.Draw{}
    case head <> tail:
      head

def combine(view: Rules.View, values: List<&2, Game.Outcome>) -> Game.Outcome:
  match view values:
    case Rules.Stop{result} _:
      result
    case Rules.Play{turn, children} Nil{}:
      Game.Draw{}
    case Rules.Play{turn, children} head <> tail:
      Pawnless.fold(tail, turn, head)

def single(remaining: Nat, positions: List<&2, Chess.Position>, +moves: Nat) -> List<&2, Game.Outcome>:
  match remaining positions:
    case _ Nil{}:
      Nil{}
    case 0n head <> tail:
      Game.evaluate(Rules.boundary(Rules.view(moves, head))) <> single(0n, tail, moves)
    case 1n++clock head <> tail:
      +node = Rules.view(moves, head)
      combine(node, single(clock, Rules.children(node), moves)) <> single(1n+clock, tail, moves)

# A four-man game enters single() at the first capture, with a fresh clock.
# This is a material transition, not a fixed total-ply search cutoff. At the
# boundary, an already-delivered mate is recognized before a clock draw.
def forest(+remaining: Nat, positions: List<&2, Chess.Position>, +limit: Nat, +moves: Nat) -> List<&2, Game.Outcome>:
  match remaining positions:
    case _ Nil{}:
      Nil{}
    case _ Chess.Position{turn, wk, bk, Nil{}} <> tail:
      Game.Draw{} <> forest(remaining, tail, limit, moves)
    case _ Chess.Position{turn, wk, bk, man <> Nil{}} <> tail:
      position = {Chess.Position{turn, wk, bk, man <> Nil{}} : Chess.Position}
      first(single(limit, position <> Nil{}, moves)) <> forest(remaining, tail, limit, moves)
    case 0n Chess.Position{turn, wk, bk, a <> b <> Nil{}} <> tail:
      position = {Chess.Position{turn, wk, bk, a <> b <> Nil{}} : Chess.Position}
      Game.evaluate(Rules.boundary(Rules.view(moves, position))) <> forest(0n, tail, limit, moves)
    case 1n++clock Chess.Position{turn, wk, bk, a <> b <> Nil{}} <> tail:
      position = {Chess.Position{turn, wk, bk, a <> b <> Nil{}} : Chess.Position}
      +node = Rules.view(moves, position)
      combine(node, forest(clock, Rules.children(node), limit, moves)) <> forest(1n+clock, tail, limit, moves)
    case _ head <> tail:
      Game.Draw{} <> forest(remaining, tail, limit, moves)

def value(+limit: Nat, moves: Nat, position: Chess.Position) -> Game.Outcome:
  first(forest(limit, position <> Nil{}, limit, moves))
