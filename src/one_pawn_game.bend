import Base
import ./game.bend as Game
import ./pawnless_chess.bend as Three
import ./pawn_chess.bend as Pawn
import ./four_chess.bend as Four
import ./one_pawn_chess.bend as Chess

type View is Data:
  Stop{outcome: Game.Outcome}
  Play{turn: Game.Player, edges: List<&2, Chess.Edge>}

def view.edges(+advance: Nat, +position: Chess.Position, edges: List<&2, Chess.Edge>) -> View:
  match edges:
    case Nil{}:
      Stop{Three.mate(Chess.checked(advance, position, Chess.turn(position)), Chess.turn(position))}
    case head <> tail:
      Play{Chess.turn(position), head <> tail}

def view.valid(valid: Bool, moves: Nat, +advance: Nat, +position: Chess.Position) -> View:
  match valid:
    case False{}:
      Stop{Game.Draw{}}
    case True{}:
      view.edges(advance, position, Chess.successors(moves, advance, position))

def view(moves: Nat, +advance: Nat, +position: Chess.Position) -> View:
  view.valid(Chess.valid(advance, position), moves, advance, position)

def boundary(view: View) -> Game.Tree:
  match view:
    case Stop{outcome}:
      Game.End{outcome}
    case Play{turn, edges}:
      Game.End{Game.Draw{}}

def assemble(view: View, trees: List<&2, Game.Tree>) -> Game.Tree:
  match view trees:
    case Stop{outcome} _:
      Game.End{outcome}
    case Play{turn, edges} Nil{}:
      Game.End{Game.Draw{}}
    case Play{turn, edges} head <> tail:
      Three.choices(tail, turn, head)

type Task is Data:
  Here{position: Chess.Position}
  Follow{edge: Chess.Edge}

def edges(items: List<&2, Chess.Edge>) -> List<&2, Task>:
  match items:
    case Nil{}:
      Nil{}
    case edge <> tail:
      Follow{edge} <> edges(tail)

def tasks(view: View) -> List<&2, Task>:
  match view:
    case Stop{outcome}:
      Nil{}
    case Play{turn, children}:
      edges(children)

# Structural ordering: actual pawn distance, remaining clock, expansion stage,
# list length. Captures leave this material class; promotion leaves pawn chess.
# Every pawn move or capture enters its continuation with the full clock.
def forest(advance: Nat, remaining: Nat, stage: Nat, items: List<&2, Task>,
  +limit: Nat, +moves: Nat, +other_moves: Nat) -> List<&2, Game.Tree>:
  match advance remaining stage items:
    case _ _ _ Nil{}:
      Nil{}
    case 1n++prior 0n 1n Here{position} <> tail:
      boundary(view(moves, 1n+prior, position)) <> forest(1n+prior, 0n, 1n, tail, limit, moves, other_moves)
    case 1n++prior 1n++clock 1n Here{position} <> tail:
      +node = view(moves, 1n+prior, position)
      assemble(node, forest(1n+prior, 1n+clock, 0n, tasks(node), limit, moves, other_moves)) <>
        forest(1n+prior, 1n+clock, 1n, tail, limit, moves, other_moves)
    case 1n++prior 1n++clock 0n Follow{Chess.Quiet{position}} <> tail:
      Three.only(forest(1n+prior, clock, 1n, Here{position} <> Nil{}, limit, moves, other_moves)) <>
        forest(1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves)
    case 1n++prior 1n++clock 0n Follow{Chess.Push{position}} <> tail:
      Three.only(forest(prior, limit, 1n, Here{position} <> Nil{}, limit, moves, other_moves)) <>
        forest(1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves)
    case 1n+1n++prior 1n++clock 0n Follow{Chess.DoublePush{position}} <> tail:
      Three.only(forest(prior, limit, 1n, Here{position} <> Nil{}, limit, moves, other_moves)) <>
        forest(1n+1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves)
    case 1n++prior 1n++clock 0n Follow{Chess.KPK{board}} <> tail:
      Pawn.tree(limit, board) <> forest(1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves)
    case 1n++prior 1n++clock 0n Follow{Chess.Pawnless{position}} <> tail:
      Four.tree(limit, other_moves, position) <> forest(1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves)
    case _ _ _ head <> tail:
      Game.End{Game.Draw{}} <> forest(advance, remaining, stage, tail, limit, moves, other_moves)

def tree(+limit: Nat, moves: Nat, other_moves: Nat, advance: Nat, position: Chess.Position) -> Game.Tree:
  Three.only(forest(advance, limit, 1n, Here{position} <> Nil{}, limit, moves, other_moves))
