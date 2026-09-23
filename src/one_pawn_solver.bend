import Base
import ./game.bend as Game
import ./pawn_chess.bend as Pawn
import ./one_pawn_chess.bend as Chess
import ./one_pawn_game.bend as Rules
import ./four_solver.bend as FourSolver
import ./pawnless_tables.bend as Fold

# Pure reference solver. No generation or performance claim is made.
# KPK is a lower-material leaf, evaluated using its existing game definition.
def combine(view: Rules.View, values: List<&2, Game.Outcome>) -> Game.Outcome:
  match view values:
    case Rules.Stop{outcome} _:
      outcome
    case Rules.Play{turn, edges} Nil{}:
      Game.Draw{}
    case Rules.Play{turn, edges} head <> tail:
      Fold.fold(tail, turn, head)

def forest(advance: Nat, remaining: Nat, stage: Nat, items: List<&2, Rules.Task>,
  +limit: Nat, +moves: Nat, +other_moves: Nat) -> List<&2, Game.Outcome>:
  match advance remaining stage items:
    case _ _ _ Nil{}:
      Nil{}
    case 1n++prior 0n 1n Rules.Here{position} <> tail:
      Game.evaluate(Rules.boundary(Rules.view(moves, 1n+prior, position))) <> forest(1n+prior, 0n, 1n, tail, limit, moves, other_moves)
    case 1n++prior 1n++clock 1n Rules.Here{position} <> tail:
      +node = Rules.view(moves, 1n+prior, position)
      combine(node, forest(1n+prior, 1n+clock, 0n, Rules.tasks(node), limit, moves, other_moves)) <>
        forest(1n+prior, 1n+clock, 1n, tail, limit, moves, other_moves)
    case 1n++prior 1n++clock 0n Rules.Follow{Chess.Quiet{position}} <> tail:
      FourSolver.first(forest(1n+prior, clock, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves)) <>
        forest(1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves)
    case 1n++prior 1n++clock 0n Rules.Follow{Chess.Push{position}} <> tail:
      FourSolver.first(forest(prior, limit, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves)) <>
        forest(1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves)
    case 1n+1n++prior 1n++clock 0n Rules.Follow{Chess.DoublePush{position}} <> tail:
      FourSolver.first(forest(prior, limit, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves)) <>
        forest(1n+1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves)
    case 1n++prior 1n++clock 0n Rules.Follow{Chess.KPK{board}} <> tail:
      Game.evaluate(Pawn.tree(limit, board)) <> forest(1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves)
    case 1n++prior 1n++clock 0n Rules.Follow{Chess.Pawnless{position}} <> tail:
      FourSolver.value(limit, other_moves, position) <> forest(1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves)
    case _ _ _ head <> tail:
      Game.Draw{} <> forest(advance, remaining, stage, tail, limit, moves, other_moves)

def value(+limit: Nat, moves: Nat, other_moves: Nat, advance: Nat, position: Chess.Position) -> Game.Outcome:
  FourSolver.first(forest(advance, limit, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves))
