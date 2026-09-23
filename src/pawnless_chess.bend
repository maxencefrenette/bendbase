import Base
import ./game.bend as Game
import ./finite_table.bend as Finite
import ./geometry.bend as Geometry

type Material is Data:
  Queen{}
  Rook{}
  Bishop{}
  Knight{}

# Squares are six-bit MSB-first words (a1=0, h8=63). Both piece ownership
# and the side to move are explicit. Castling rights are outside this domain.
type Board is Data:
  Board{owner: Game.Player, turn: Game.Player,
    wk: Word(6n), bk: Word(6n), pc: Word(6n)}

type State is Data:
  Three{board: Board}
  KingsOnly{}

type Move is Data:
  KingMove{dest: Word(6n)}
  PieceMove{dest: Word(6n)}

def number(n: Nat, bits: Word(n)) -> U32:
  match n bits:
    case 0n WNil{}:
      0
    case 1n++rest WCon{bit, tail}:
      (Bool.pick(U32, bit, U32.shln(1, rest), 0) + number(rest, tail) : U32)

def same(left: Game.Player, right: Game.Player) -> Bool:
  match left right:
    case Game.White{} Game.White{}:
      True{}
    case Game.Black{} Game.Black{}:
      True{}
    case _ _:
      False{}

def other(player: Game.Player) -> Game.Player:
  match player:
    case Game.White{}:
      Game.Black{}
    case Game.Black{}:
      Game.White{}

def kind(material: Material) -> U32:
  match material:
    case Queen{}:
      0
    case Rook{}:
      1
    case Bishop{}:
      2
    case Knight{}:
      3

def insufficient(material: Material) -> Bool:
  match material:
    case Bishop{}:
      True{}
    case Knight{}:
      True{}
    case _:
      False{}

def king(board: Board, player: Game.Player) -> Word(6n):
  match board player:
    case Board{owner, turn, wk, bk, pc} Game.White{}:
      wk
    case Board{owner, turn, wk, bk, pc} Game.Black{}:
      bk

def checked(material: Material, +board: Board, +player: Game.Player) -> Bool:
  match board:
    case Board{+owner, turn, +wk, +bk, pc}:
      Geometry.kings_touch(number(6n, wk), number(6n, bk)) ||
      (Bool.not(same(owner, player)) &&
       Geometry.attacks(kind(material), number(6n, pc),
         number(6n, king(board, player)), number(6n, king(board, owner))))

def valid(+material: Material, +board: Board) -> Bool:
  match board:
    case Board{owner, +turn, +wk, +bk, +pc}:
      U32.is_ne(number(6n, wk), number(6n, bk)) &&
      U32.is_ne(number(6n, wk), number(6n, pc)) &&
      U32.is_ne(number(6n, bk), number(6n, pc)) &&
      Bool.not(Geometry.kings_touch(number(6n, wk), number(6n, bk))) &&
      Bool.not(checked(material, board, other(turn)))

def after_king(board: Board, dest: Word(6n)) -> Board:
  match board:
    case Board{owner, Game.White{}, wk, bk, pc}:
      Board{owner, Game.Black{}, dest, bk, pc}
    case Board{owner, Game.Black{}, wk, bk, pc}:
      Board{owner, Game.White{}, wk, dest, pc}

def after_piece(board: Board, dest: Word(6n)) -> Board:
  match board:
    case Board{owner, turn, wk, bk, pc}:
      Board{owner, other(turn), wk, bk, dest}

def capture(+board: Board, move: Move) -> Bool:
  match board move:
    case Board{owner, turn, wk, bk, pc} KingMove{dest}:
      Bool.not(same(owner, turn)) && U32.is_eq(number(6n, dest), number(6n, pc))
    case _ _:
      False{}

def legal(+material: Material, +board: Board, move: Move) -> Bool:
  match board move:
    case Board{+owner, +turn, +wk, +bk, +pc} KingMove{+dest}:
      valid(material, board) &&
      Geometry.king_step(number(6n, king(board, turn)), number(6n, dest)) &&
      ((capture(board, KingMove{dest}) &&
        Bool.not(Geometry.kings_touch(number(6n, dest), number(6n, king(board, other(turn)))))) ||
       valid(material, after_king(board, dest)))
    case Board{+owner, +turn, +wk, +bk, +pc} PieceMove{+dest}:
      valid(material, board) && same(owner, turn) &&
      Geometry.piece_step(kind(material), number(6n, pc), number(6n, dest),
        number(6n, wk), number(6n, bk)) && valid(material, after_piece(board, dest))

def after.if(captured: Bool, board: Board) -> State:
  match captured:
    case True{}:
      KingsOnly{}
    case False{}:
      Three{board}

def after(+board: Board, move: Move) -> State:
  match move:
    case KingMove{+dest}:
      after.if(capture(board, KingMove{dest}), after_king(board, dest))
    case PieceMove{dest}:
      Three{after_piece(board, dest)}

def action(key: Word(7n)) -> Move:
  match key:
    case WCon{False{}, dest}:
      KingMove{dest}
    case WCon{True{}, dest}:
      PieceMove{dest}

def include(legal: Bool, next: State, tail: List<&2, State>) -> List<&2, State>:
  match legal:
    case True{}:
      next <> tail
    case False{}:
      tail

# The domain of moves is exactly one piece-selection bit and six square bits.
# The canonical finite table enumerates every such key, structurally.
def successors.go(depth: Nat, +material: Material, +board: Board,
  keys: Finite.Table(depth, Word(7n)), tail: List<&2, State>) -> List<&2, State>:
  match depth keys:
    case 0n +key:
      include(legal(material, board, action(key)), after(board, action(key)), tail)
    case 1n++rest Finite.Fork{left, right}:
      successors.go(rest, material, board, left,
        successors.go(rest, material, board, right, tail))

def successors(material: Material, board: Board) -> List<&2, State>:
  successors.go(7n, material, board, Finite.keys(7n), Nil{})

type View is Data:
  Stop{outcome: Game.Outcome}
  Play{turn: Game.Player, children: List<&2, State>}

def mate(checked: Bool, turn: Game.Player) -> Game.Outcome:
  match checked turn:
    case False{} _:
      Game.Draw{}
    case True{} Game.White{}:
      Game.BlackWin{}
    case True{} Game.Black{}:
      Game.WhiteWin{}

def view.moves(+material: Material, +board: Board, children: List<&2, State>) -> View:
  match board children:
    case Board{owner, +turn, wk, bk, pc} Nil{}:
      Stop{mate(checked(material, board, turn), turn)}
    case Board{owner, turn, wk, bk, pc} +head <> +tail:
      Play{turn, head <> tail}

def view.live(live: Bool, +material: Material, +board: Board) -> View:
  match live:
    case False{}:
      Stop{Game.Draw{}}
    case True{}:
      view.moves(material, board, successors(material, board))

def view(+material: Material, state: State) -> View:
  match state:
    case KingsOnly{}:
      Stop{Game.Draw{}}
    case Three{+board}:
      view.live(valid(material, board) && Bool.not(insufficient(material)), material, board)

def children(view: View) -> List<&2, State>:
  match view:
    case Stop{outcome}:
      Nil{}
    case Play{turn, children}:
      children

def boundary(view: View) -> Game.Tree:
  match view:
    case Stop{outcome}:
      Game.End{outcome}
    case Play{turn, children}:
      Game.End{Game.Draw{}}

def choices(rest: List<&2, Game.Tree>, +turn: Game.Player, first: Game.Tree) -> Game.Tree:
  match rest:
    case Nil{}:
      first
    case head <> tail:
      Game.Choose{turn, first, choices(tail, turn, head)}

def assemble(view: View, children: List<&2, Game.Tree>) -> Game.Tree:
  match view children:
    case Stop{outcome} _:
      Game.End{outcome}
    case Play{turn, states} Nil{}:
      Game.End{Game.Draw{}}
    case Play{turn, states} head <> tail:
      choices(tail, turn, head)

# This is the game specified by the chess rules, with a remaining halfmove
# allowance. Capture ends in KingsOnly; every continuing move consumes one.
# At zero allowance, view still recognizes checkmate before the clock draw.
def forest(remaining: Nat, +material: Material, states: List<&2, State>) -> List<&2, Game.Tree>:
  match remaining states:
    case _ Nil{}:
      Nil{}
    case 0n head <> tail:
      boundary(view(material, head)) <> forest(0n, material, tail)
    case 1n++rest head <> tail:
      +node = view(material, head)
      assemble(node, forest(rest, material, children(node))) <>
        forest(1n+rest, material, tail)

def only(trees: List<&2, Game.Tree>) -> Game.Tree:
  match trees:
    case Nil{}:
      Game.End{Game.Draw{}}
    case head <> tail:
      head

def tree(remaining: Nat, material: Material, board: Board) -> Game.Tree:
  only(forest(remaining, material, Three{board} <> Nil{}))

def Member(+state: State, states: List<&2, State>) -> Type:
  match states:
    case Nil{}:
      Empty
    case head <> tail:
      {state == head : State} | Member(state, tail)

def LegalSuccessor(+material: Material, +board: Board, +state: State) -> Type:
  &key: Word(7n) ->
    Game.Truth(legal(material, board, action(key))) &
    {state == after(board, action(key)) : State}
