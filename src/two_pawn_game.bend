import Base
import ./game.bend as Game
import ./pawnless_chess.bend as Three
import ./pawn_chess.bend as Pawn
import ./four_chess.bend as Four
import ./one_pawn_game.bend as One
import ./two_pawn_chess.bend as Chess

type View is Data:
  Stop{outcome: Game.Outcome}
  Play{turn: Game.Player, edges: List<&2, Chess.Edge>}

def view.edges(+a: Nat, +b: Nat, +position: Chess.Position, edges: List<&2, Chess.Edge>) -> View:
  match edges:
    case Nil{}:
      Stop{Three.mate(Chess.checked(a, b, position, Chess.turn(position)), Chess.turn(position))}
    case head <> tail:
      Play{Chess.turn(position), head <> tail}

def view.valid(valid: Bool, moves: Nat, +a: Nat, +b: Nat, +position: Chess.Position) -> View:
  match valid:
    case False{}:
      Stop{Game.Draw{}}
    case True{}:
      view.edges(a, b, position, Chess.successors(moves, a, b, position))

def view(moves: Nat, +a: Nat, +b: Nat, +position: Chess.Position) -> View:
  view.valid(Chess.valid(a, b, position), moves, a, b, position)

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

# Lexicographic structural recursion on the two ACTUAL distances to promotion,
# remaining reversible halfmoves, expansion stage, and task list. No arbitrary
# search fuel: pushes decrease a distance; captures/promotions leave this domain.
# Every zeroing move (including EP) enters its continuation with a fresh clock.
def forest(a: Nat, b: Nat, remaining: Nat, stage: Nat, items: List<&2, Task>,
  +limit: Nat, +moves: Nat, +other_moves: Nat) -> List<&2, Game.Tree>:
  match a b remaining stage items:
    case _ _ _ _ Nil{}:
      Nil{}
    case 1n++pa 1n++pb 0n 1n Here{position} <> tail:
      boundary(view(moves, 1n+pa, 1n+pb, position)) <> forest(1n+pa, 1n+pb, 0n, 1n, tail, limit, moves, other_moves)
    case 1n++pa 1n++pb 1n++clock 1n Here{position} <> tail:
      +node = view(moves, 1n+pa, 1n+pb, position)
      assemble(node, forest(1n+pa, 1n+pb, 1n+clock, 0n, tasks(node), limit, moves, other_moves)) <>
        forest(1n+pa, 1n+pb, 1n+clock, 1n, tail, limit, moves, other_moves)
    case 1n++pa 1n++pb 1n++clock 0n Follow{Chess.Quiet{position}} <> tail:
      Three.only(forest(1n+pa, 1n+pb, clock, 1n, Here{position} <> Nil{}, limit, moves, other_moves)) <>
        forest(1n+pa, 1n+pb, 1n+clock, 0n, tail, limit, moves, other_moves)
    case 1n++pa 1n++pb 1n++clock 0n Follow{Chess.FirstPush{position}} <> tail:
      Three.only(forest(pa, 1n+pb, limit, 1n, Here{position} <> Nil{}, limit, moves, other_moves)) <>
        forest(1n+pa, 1n+pb, 1n+clock, 0n, tail, limit, moves, other_moves)
    case 1n+1n++pa 1n++pb 1n++clock 0n Follow{Chess.FirstDouble{position}} <> tail:
      Three.only(forest(pa, 1n+pb, limit, 1n, Here{position} <> Nil{}, limit, moves, other_moves)) <>
        forest(1n+1n+pa, 1n+pb, 1n+clock, 0n, tail, limit, moves, other_moves)
    case 1n++pa 1n++pb 1n++clock 0n Follow{Chess.SecondPush{position}} <> tail:
      Three.only(forest(1n+pa, pb, limit, 1n, Here{position} <> Nil{}, limit, moves, other_moves)) <>
        forest(1n+pa, 1n+pb, 1n+clock, 0n, tail, limit, moves, other_moves)
    case 1n++pa 1n+1n++pb 1n++clock 0n Follow{Chess.SecondDouble{position}} <> tail:
      Three.only(forest(1n+pa, pb, limit, 1n, Here{position} <> Nil{}, limit, moves, other_moves)) <>
        forest(1n+pa, 1n+1n+pb, 1n+clock, 0n, tail, limit, moves, other_moves)
    case 1n++pa 1n++pb 1n++clock 0n Follow{Chess.KPK{board}} <> tail:
      Pawn.tree(limit, board) <> forest(1n+pa, 1n+pb, 1n+clock, 0n, tail, limit, moves, other_moves)
    case 1n++pa 1n++pb 1n++clock 0n Follow{Chess.Promoted{advance, position}} <> tail:
      One.tree(limit, moves, other_moves, advance, position) <>
        forest(1n+pa, 1n+pb, 1n+clock, 0n, tail, limit, moves, other_moves)
    case 1n++pa 1n++pb 1n++clock 0n Follow{Chess.Pawnless{position}} <> tail:
      Four.tree(limit, other_moves, position) <> forest(1n+pa, 1n+pb, 1n+clock, 0n, tail, limit, moves, other_moves)
    case _ _ _ _ head <> tail:
      Game.End{Game.Draw{}} <> forest(a, b, remaining, stage, tail, limit, moves, other_moves)

def tree(+limit: Nat, moves: Nat, other_moves: Nat, a: Nat, b: Nat, position: Chess.Position) -> Game.Tree:
  Three.only(forest(a, b, limit, 1n, Here{position} <> Nil{}, limit, moves, other_moves))
