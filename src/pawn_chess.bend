import Base
import ./game.bend as Game
import ./pawnless_chess.bend as Chess
import ./geometry.bend as Geometry
import ./finite_table.bend as Finite

# advance is the pawn's actual distance to promotion: 1 on the seventh rank
# from its owner's perspective, 6 on its starting rank. It is not a search budget.
type Position is Data:
  Position{owner: Game.Player, turn: Game.Player, wk: Word(6n), bk: Word(6n), file: Word(3n)}

type Action is Data:
  King{dest: Word(6n)}
  Step{}
  Double{}
  Promotion{material: Chess.Material}
  Unused{}

type Edge is Data:
  Quiet{position: Position}
  Push{position: Position}
  DoublePush{position: Position}
  Promoted{material: Chess.Material, board: Chess.Board}
  Captured{}

def rank(advance: Nat, owner: Game.Player) -> Word(3n):
  match advance owner:
    case 0n Game.White{}:
      WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}
    case 0n Game.Black{}:
      WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}
    case 1n Game.White{}:
      WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}
    case 1n Game.Black{}:
      WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}
    case 2n Game.White{}:
      WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}
    case 2n Game.Black{}:
      WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}
    case 3n Game.White{}:
      WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}
    case 3n Game.Black{}:
      WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}
    case 4n Game.White{}:
      WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}
    case 4n Game.Black{}:
      WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}
    case 5n Game.White{}:
      WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}
    case 5n Game.Black{}:
      WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}
    case 6n Game.White{}:
      WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}
    case 6n Game.Black{}:
      WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}
    case _ Game.White{}:
      WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}
    case _ Game.Black{}:
      WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}

def distance(owner: Game.Player, rank: Word(3n)) -> Nat:
  match owner rank:
    case Game.White{} WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}:
      6n
    case Game.White{} WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}:
      5n
    case Game.White{} WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}:
      4n
    case Game.White{} WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}:
      3n
    case Game.White{} WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}:
      2n
    case Game.White{} WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}:
      1n
    case Game.Black{} WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}:
      1n
    case Game.Black{} WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}:
      2n
    case Game.Black{} WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}:
      3n
    case Game.Black{} WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}:
      4n
    case Game.Black{} WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}:
      5n
    case Game.Black{} WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}:
      6n
    case _ _:
      0n

def square(rank: Word(3n), file: Word(3n)) -> Word(6n):
  match rank:
    case WCon{a, WCon{b, WCon{c, WNil{}}}}:
      WCon{a, WCon{b, WCon{c, file}}}

def board(+advance: Nat, position: Position) -> Chess.Board:
  match position:
    case Position{+owner, turn, wk, bk, file}:
      Chess.Board{owner, turn, wk, bk, square(rank(advance, owner), file)}

def position(board: Chess.Board) -> Position:
  match board:
    case Chess.Board{owner, turn, wk, bk, WCon{a, WCon{b, WCon{c, file}}}}:
      Position{owner, turn, wk, bk, file}

def advance(board: Chess.Board) -> Nat:
  match board:
    case Chess.Board{owner, turn, wk, bk, WCon{a, WCon{b, WCon{c, file}}}}:
      distance(owner, WCon{a, WCon{b, WCon{c, WNil{}}}})

def on_board(advance: Nat) -> Bool:
  match advance:
    case 1n:
      True{}
    case 2n:
      True{}
    case 3n:
      True{}
    case 4n:
      True{}
    case 5n:
      True{}
    case 6n:
      True{}
    case _:
      False{}

def forward(owner: Game.Player, +from: U32, +to: U32) -> Bool:
  match owner:
    case Game.White{}:
      U32.is_eq(Geometry.rank(to), (Geometry.rank(from) + 1 : U32))
    case Game.Black{}:
      U32.is_eq(Geometry.rank(from), (Geometry.rank(to) + 1 : U32))

def attacks(+advance: Nat, +position: Position, target: Word(6n)) -> Bool:
  match position:
    case Position{+owner, turn, wk, bk, file}:
      +pc = Chess.number(6n, square(rank(advance, owner), file))
      +dest = Chess.number(6n, target)
      forward(owner, pc, dest) && U32.is_eq(Geometry.distance(Geometry.file(pc), Geometry.file(dest)), 1)

def checked(+advance: Nat, +position: Position, +player: Game.Player) -> Bool:
  match position:
    case Position{+owner, turn, +wk, +bk, file}:
      Geometry.kings_touch(Chess.number(6n, wk), Chess.number(6n, bk)) ||
      (Bool.not(Chess.same(owner, player)) && attacks(advance, position, Chess.king(board(advance, position), player)))

def valid(+advance: Nat, +position: Position) -> Bool:
  match position:
    case Position{+owner, +turn, +wk, +bk, +file}:
      +pc = Chess.number(6n, square(rank(advance, owner), file))
      on_board(advance) &&
      U32.is_ne(Chess.number(6n, wk), Chess.number(6n, bk)) &&
      U32.is_ne(Chess.number(6n, wk), pc) && U32.is_ne(Chess.number(6n, bk), pc) &&
      Bool.not(Geometry.kings_touch(Chess.number(6n, wk), Chess.number(6n, bk))) &&
      Bool.not(checked(advance, position, Chess.other(turn)))

def valid_board(+board: Chess.Board) -> Bool:
  valid(advance(board), position(board))

def after_king(position: Position, dest: Word(6n)) -> Position:
  match position:
    case Position{owner, Game.White{}, wk, bk, file}:
      Position{owner, Game.Black{}, dest, bk, file}
    case Position{owner, Game.Black{}, wk, bk, file}:
      Position{owner, Game.White{}, wk, dest, file}

def after_push(position: Position) -> Position:
  match position:
    case Position{owner, turn, wk, bk, file}:
      Position{owner, Chess.other(turn), wk, bk, file}

def empty(+advance: Nat, position: Position) -> Bool:
  match position:
    case Position{owner, turn, wk, bk, file}:
      +dest = Chess.number(6n, square(rank(advance, owner), file))
      U32.is_ne(dest, Chess.number(6n, wk)) && U32.is_ne(dest, Chess.number(6n, bk))

def capture(+advance: Nat, +position: Position, dest: Word(6n)) -> Bool:
  match position:
    case Position{+owner, turn, wk, bk, file}:
      Bool.not(Chess.same(owner, turn)) &&
      U32.is_eq(Chess.number(6n, dest), Chess.number(6n, square(rank(advance, owner), file)))

def owns_turn(position: Position) -> Bool:
  match position:
    case Position{owner, turn, wk, bk, file}:
      Chess.same(owner, turn)

def turn(position: Position) -> Game.Player:
  match position:
    case Position{owner, turn, wk, bk, file}:
      turn

def legal(+advance: Nat, +position: Position, action: Action) -> Bool:
  match advance action:
    case _ King{+dest}:
      valid(advance, position) &&
      Geometry.king_step(Chess.number(6n, Chess.king(board(advance, position),
        turn(position))), Chess.number(6n, dest)) &&
      ((capture(advance, position, dest) &&
        Bool.not(Geometry.kings_touch(Chess.number(6n, dest),
          Chess.number(6n, Chess.king(board(advance, position), Chess.other(turn(position))))))) ||
       valid(advance, after_king(position, dest)))
    case 1n+1n+rest Step{}:
      valid(advance, position) && owns_turn(position) && empty(1n+rest, position)
    case 6n Double{}:
      valid(advance, position) && owns_turn(position) && empty(5n, position) && empty(4n, position)
    case 1n Promotion{+material}:
      valid(advance, position) && owns_turn(position) && empty(0n, position) &&
      Chess.valid(material, board(0n, after_push(position)))
    case _ _:
      False{}

def after.capture(captured: Bool, position: Position) -> Edge:
  match captured:
    case True{}:
      Captured{}
    case False{}:
      Quiet{position}

def after(+advance: Nat, +position: Position, action: Action) -> Edge:
  match action:
    case King{+dest}:
      after.capture(capture(advance, position, dest), after_king(position, dest))
    case Step{}:
      Push{after_push(position)}
    case Double{}:
      DoublePush{after_push(position)}
    case Promotion{material}:
      Promoted{material, board(0n, after_push(position))}
    case Unused{}:
      Captured{}

# 0..63 are king destinations. 64/65 are single/double pushes, 66..69
# promote to Q/R/B/N. The remaining keys are explicitly illegal.
def action(key: Word(7n)) -> Action:
  match key:
    case WCon{False{}, dest}:
      King{dest}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}:
      Step{}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}:
      Double{}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}:
      Promotion{Chess.Queen{}}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}:
      Promotion{Chess.Rook{}}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}:
      Promotion{Chess.Bishop{}}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}:
      Promotion{Chess.Knight{}}
    case _:
      Unused{}

def include(legal: Bool, edge: Edge, tail: List<&2, Edge>) -> List<&2, Edge>:
  match legal:
    case True{}:
      edge <> tail
    case False{}:
      tail

def successors.go(depth: Nat, +advance: Nat, +position: Position,
  keys: Finite.Table(depth, Word(7n)), tail: List<&2, Edge>) -> List<&2, Edge>:
  match depth keys:
    case 0n +key:
      include(legal(advance, position, action(key)), after(advance, position, action(key)), tail)
    case 1n++rest Finite.Fork{left, right}:
      successors.go(rest, advance, position, left, successors.go(rest, advance, position, right, tail))

def successors(advance: Nat, position: Position) -> List<&2, Edge>:
  successors.go(7n, advance, position, Finite.keys(7n), Nil{})

type View is Data:
  Stop{outcome: Game.Outcome}
  Play{turn: Game.Player, edges: List<&2, Edge>}

def view.edges(+advance: Nat, +position: Position, edges: List<&2, Edge>) -> View:
  match edges:
    case Nil{}:
      Stop{Chess.mate(checked(advance, position, turn(position)), turn(position))}
    case head <> tail:
      Play{turn(position), head <> tail}

def view.valid(valid: Bool, +advance: Nat, +position: Position) -> View:
  match valid:
    case False{}:
      Stop{Game.Draw{}}
    case True{}:
      view.edges(advance, position, successors(advance, position))

def view(+advance: Nat, +position: Position) -> View:
  view.valid(valid(advance, position), advance, position)

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
      Chess.choices(tail, turn, head)

type Task is Data:
  Here{position: Position}
  Follow{edge: Edge}

def moves(edges: List<&2, Edge>) -> List<&2, Task>:
  match edges:
    case Nil{}:
      Nil{}
    case edge <> tail:
      Follow{edge} <> moves(tail)

def tasks(view: View) -> List<&2, Task>:
  match view:
    case Stop{outcome}:
      Nil{}
    case Play{turn, edges}:
      moves(edges)

# Lexicographic recursion: pawn distance, remaining clock, expansion stage,
# then list length. Stage 1 expands a position; stage 0 follows its legal moves.
# A push reduces actual pawn distance and resets the clock to limit; promotion
# enters the existing pawnless game at that same reset clock.
def forest(advance: Nat, remaining: Nat, stage: Nat, items: List<&2, Task>, +limit: Nat) -> List<&2, Game.Tree>:
  match advance remaining stage items:
    case _ _ _ Nil{}:
      Nil{}
    case 1n++prior 0n 1n Here{position} <> tail:
      boundary(view(1n+prior, position)) <> forest(1n+prior, 0n, 1n, tail, limit)
    case 1n++prior 1n++clock 1n Here{position} <> tail:
      +node = view(1n+prior, position)
      assemble(node, forest(1n+prior, 1n+clock, 0n, tasks(node), limit)) <>
        forest(1n+prior, 1n+clock, 1n, tail, limit)
    case 1n++prior 1n++clock 0n Follow{Quiet{position}} <> tail:
      Chess.only(forest(1n+prior, clock, 1n, Here{position} <> Nil{}, limit)) <>
        forest(1n+prior, 1n+clock, 0n, tail, limit)
    case 1n++prior 1n++clock 0n Follow{Push{position}} <> tail:
      Chess.only(forest(prior, limit, 1n, Here{position} <> Nil{}, limit)) <>
        forest(1n+prior, 1n+clock, 0n, tail, limit)
    case 1n+1n++prior 1n++clock 0n Follow{DoublePush{position}} <> tail:
      Chess.only(forest(prior, limit, 1n, Here{position} <> Nil{}, limit)) <>
        forest(1n+1n+prior, 1n+clock, 0n, tail, limit)
    case 1n++prior 1n++clock 0n Follow{Promoted{material, board}} <> tail:
      Chess.tree(limit, material, board) <> forest(1n+prior, 1n+clock, 0n, tail, limit)
    case _ _ _ head <> tail:
      Game.End{Game.Draw{}} <> forest(advance, remaining, stage, tail, limit)

def tree(+limit: Nat, +input: Chess.Board) -> Game.Tree:
  Chess.only(forest(advance(input), limit, 1n, Here{position(input)} <> Nil{}, limit))

def Member(+edge: Edge, edges: List<&2, Edge>) -> Type:
  match edges:
    case Nil{}:
      Empty
    case head <> tail:
      {edge == head : Edge} | Member(edge, tail)

def LegalSuccessor(+advance: Nat, +position: Position, +edge: Edge) -> Type:
  &key: Word(7n) ->
    Game.Truth(legal(advance, position, action(key))) &
    {edge == after(advance, position, action(key)) : Edge}
