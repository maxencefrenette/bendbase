import Base
import ./game.bend as Game
import ./pawnless_chess.bend as Three
import ./material_chess.bend as Chess
import ./geometry.bend as Geometry

# Independent game semantics over the material-independent move rules.
# No board enumeration, table lookups or solver certificates occur here.
def color(square: Word(6n)) -> U32:
  +n = Three.number(6n, square)
  U32.and((Geometry.file(n) + Geometry.rank(n) : U32), 1)

def insufficient(men: List<&2, Chess.Man>) -> Bool:
  match men:
    case Nil{}:
      True{}
    case Chess.Man{owner, kind, square} <> Nil{}:
      Three.insufficient(kind)
    case Chess.Man{a, Three.Bishop{}, x} <> Chess.Man{b, Three.Bishop{}, y} <> Nil{}:
      U32.is_eq(color(x), color(y))
    case _:
      False{}

type View is Data:
  Stop{result: Game.Outcome}
  Play{turn: Game.Player, children: List<&2, Chess.Position>}

def view.moves(+position: Chess.Position, children: List<&2, Chess.Position>) -> View:
  match position children:
    case Chess.Position{+turn, wk, bk, men} Nil{}:
      Stop{Three.mate(Chess.checked(position, turn), turn)}
    case Chess.Position{turn, wk, bk, men} head <> tail:
      Play{turn, head <> tail}

def view.live(live: Bool, moves: Nat, +position: Chess.Position) -> View:
  match live:
    case False{}:
      Stop{Game.Draw{}}
    case True{}:
      view.moves(position, Chess.successors(moves, position))

def view(moves: Nat, +position: Chess.Position) -> View:
  match position:
    case Chess.Position{turn, wk, bk, men}:
      view.live(Chess.valid(position) && Bool.not(insufficient(men)), moves, position)

def children(view: View) -> List<&2, Chess.Position>:
  match view:
    case Stop{result}:
      Nil{}
    case Play{turn, children}:
      children

def boundary(view: View) -> Game.Tree:
  match view:
    case Stop{result}:
      Game.End{result}
    case Play{turn, children}:
      Game.End{Game.Draw{}}

def assemble(view: View, trees: List<&2, Game.Tree>) -> Game.Tree:
  match view trees:
    case Stop{result} _:
      Game.End{result}
    case Play{turn, children} Nil{}:
      Game.End{Game.Draw{}}
    case Play{turn, children} head <> tail:
      Three.choices(tail, turn, head)

# At most one extra piece: the only capture leaves bare kings and ends play.
# The clock can therefore count down without a continuing reset branch.
def single(remaining: Nat, positions: List<&2, Chess.Position>, +moves: Nat) -> List<&2, Game.Tree>:
  match remaining positions:
    case _ Nil{}:
      Nil{}
    case 0n head <> tail:
      boundary(view(moves, head)) <> single(0n, tail, moves)
    case 1n++clock head <> tail:
      +node = view(moves, head)
      assemble(node, single(clock, children(node), moves)) <> single(1n+clock, tail, moves)

# A four-man game enters single() at the first capture, with a fresh clock.
# This is a material transition, not a fixed total-ply search cutoff. At the
# boundary, an already-delivered mate is recognized before a clock draw.
def forest(+remaining: Nat, positions: List<&2, Chess.Position>, +limit: Nat, +moves: Nat) -> List<&2, Game.Tree>:
  match remaining positions:
    case _ Nil{}:
      Nil{}
    case _ Chess.Position{turn, wk, bk, Nil{}} <> tail:
      Game.End{Game.Draw{}} <> forest(remaining, tail, limit, moves)
    case _ Chess.Position{turn, wk, bk, man <> Nil{}} <> tail:
      position = {Chess.Position{turn, wk, bk, man <> Nil{}} : Chess.Position}
      Three.only(single(limit, position <> Nil{}, moves)) <> forest(remaining, tail, limit, moves)
    case 0n Chess.Position{turn, wk, bk, a <> b <> Nil{}} <> tail:
      position = {Chess.Position{turn, wk, bk, a <> b <> Nil{}} : Chess.Position}
      boundary(view(moves, position)) <> forest(0n, tail, limit, moves)
    case 1n++clock Chess.Position{turn, wk, bk, a <> b <> Nil{}} <> tail:
      position = {Chess.Position{turn, wk, bk, a <> b <> Nil{}} : Chess.Position}
      +node = view(moves, position)
      assemble(node, forest(clock, children(node), limit, moves)) <> forest(1n+clock, tail, limit, moves)
    case _ head <> tail:
      Game.End{Game.Draw{}} <> forest(remaining, tail, limit, moves)

def tree(+limit: Nat, moves: Nat, position: Chess.Position) -> Game.Tree:
  Three.only(forest(limit, position <> Nil{}, limit, moves))
