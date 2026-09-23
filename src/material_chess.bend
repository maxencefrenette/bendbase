import Base
import ./game.bend as Game
import ./pawnless_chess.bend as Three
import ./geometry.bend as Geometry
import ./finite_table.bend as Finite
import ./pawnless_index.bend as Index

# Material-independent pawnless move rules. Kings cannot be captured; the
# list contains only Q/R/B/N. No castling rights. Clock/terminal/table solving
# deliberately remain outside this move layer.
type Man is Data:
  Man{owner: Game.Player, kind: Three.Material, square: Word(6n)}

type Position is Data:
  Position{turn: Game.Player, wk: Word(6n), bk: Word(6n), men: List<&2, Man>}

type Action is Data:
  Action{from: Word(6n), dest: Word(6n)}

def equal(a: Word(6n), b: Word(6n)) -> Bool:
  U32.is_eq(Three.number(6n, a), Three.number(6n, b))

def occupied(men: List<&2, Man>, +square: Word(6n)) -> Bool:
  match men:
    case Nil{}:
      False{}
    case Man{owner, kind, at} <> tail:
      equal(at, square) || occupied(tail, square)

def friendly(men: List<&2, Man>, +player: Game.Player, +square: Word(6n)) -> Bool:
  match men:
    case Nil{}:
      False{}
    case Man{owner, kind, at} <> tail:
      (Three.same(owner, player) && equal(at, square)) || friendly(tail, player, square)

def distinct(men: List<&2, Man>, +wk: Word(6n), +bk: Word(6n)) -> Bool:
  match men:
    case Nil{}:
      True{}
    case Man{owner, kind, +at} <> +tail:
      Bool.not(equal(at, wk)) && Bool.not(equal(at, bk)) &&
        Bool.not(occupied(tail, at)) && distinct(tail, wk, bk)

def clear(men: List<&2, Man>, +from: Word(6n), +dest: Word(6n)) -> Bool:
  match men:
    case Nil{}:
      True{}
    case Man{owner, kind, at} <> tail:
      Bool.not(Geometry.on_segment(Three.number(6n, from), Three.number(6n, dest), Three.number(6n, at))) &&
        clear(tail, from, dest)

def king(position: Position, player: Game.Player) -> Word(6n):
  match position player:
    case Position{turn, wk, bk, men} Game.White{}:
      wk
    case Position{turn, wk, bk, men} Game.Black{}:
      bk

def attacks(+kind: Three.Material, +from: Word(6n), +dest: Word(6n), position: Position) -> Bool:
  match position:
    case Position{turn, wk, bk, men}:
      # Segment endpoints do not obstruct. Both kings and ALL extra pieces
      # obstruct sliders; knights ignore intervening pieces.
      Geometry.piece_step(Three.kind(kind), Three.number(6n, from), Three.number(6n, dest),
        Three.number(6n, wk), Three.number(6n, bk)) &&
        (U32.is_eq(Three.kind(kind), 3) || clear(men, from, dest))

def threatened(men: List<&2, Man>, +position: Position, +player: Game.Player, +target: Word(6n)) -> Bool:
  match men:
    case Nil{}:
      False{}
    case Man{owner, kind, at} <> tail:
      (Bool.not(Three.same(owner, player)) && attacks(kind, at, target, position)) ||
        threatened(tail, position, player, target)

def checked(+position: Position, +player: Game.Player) -> Bool:
  match position:
    case Position{turn, +wk, +bk, men}:
      Geometry.kings_touch(Three.number(6n, wk), Three.number(6n, bk)) ||
        threatened(men, position, player, king(position, player))

def valid(+position: Position) -> Bool:
  match position:
    case Position{+turn, +wk, +bk, men}:
      Bool.not(equal(wk, bk)) && distinct(men, wk, bk) &&
        Bool.not(Geometry.kings_touch(Three.number(6n, wk), Three.number(6n, bk))) &&
        Bool.not(checked(position, Three.other(turn)))

def move_square(+at: Word(6n), +from: Word(6n), +dest: Word(6n)) -> Word(6n):
  Bool.pick(Word(6n), equal(at, from), dest, at)

def keep(remove: Bool, man: Man, tail: List<&2, Man>) -> List<&2, Man>:
  match remove:
    case True{}:
      tail
    case False{}:
      man <> tail

def move_men(men: List<&2, Man>, +from: Word(6n), +dest: Word(6n)) -> List<&2, Man>:
  match men:
    case Nil{}:
      Nil{}
    case Man{owner, kind, +at} <> tail:
      keep(equal(at, dest), Man{owner, kind, move_square(at, from, dest)}, move_men(tail, from, dest))

def after(position: Position, action: Action) -> Position:
  match position action:
    case Position{turn, wk, bk, men} Action{+from, +dest}:
      Position{Three.other(turn), move_square(wk, from, dest), move_square(bk, from, dest), move_men(men, from, dest)}

def piece_move(men: List<&2, Man>, +position: Position, +turn: Game.Player, +from: Word(6n), +dest: Word(6n)) -> Bool:
  match men:
    case Nil{}:
      False{}
    case Man{owner, kind, +at} <> tail:
      (Three.same(owner, turn) && equal(at, from) && attacks(kind, at, dest, position)) ||
        piece_move(tail, position, turn, from, dest)

def pseudo(+position: Position, action: Action) -> Bool:
  match position action:
    case Position{+turn, +wk, +bk, +men} Action{+from, +dest}:
      Bool.not(equal(dest, wk)) && Bool.not(equal(dest, bk)) && Bool.not(friendly(men, turn, dest)) &&
        ((equal(from, king(position, turn)) && Geometry.king_step(Three.number(6n, from), Three.number(6n, dest))) ||
          piece_move(men, position, turn, from, dest))

def legal(+position: Position, +action: Action) -> Bool:
  (valid(position) && pseudo(position, action)) && valid(after(position, action))

# On legal moves an occupied destination is an enemy non-king piece. This
# flag is for the next solver's material transition and 50-move clock reset.
def capture(position: Position, action: Action) -> Bool:
  match position action:
    case Position{turn, wk, bk, men} Action{from, dest}:
      occupied(men, dest)

def action(key: Word(12n)) -> Action:
  match key:
    case WCon{a, WCon{b, WCon{c, WCon{d, WCon{e, WCon{f, dest}}}}}}:
      Action{WCon{a, WCon{b, WCon{c, WCon{d, WCon{e, WCon{f, WNil{}}}}}}}, dest}

def encode(action: Action) -> Word(12n):
  match action:
    case Action{WCon{a, WCon{b, WCon{c, WCon{d, WCon{e, WCon{f, WNil{}}}}}}}, dest}:
      WCon{a, WCon{b, WCon{c, WCon{d, WCon{e, WCon{f, dest}}}}}}

def action_at(+width: Nat, key: Word(width)) -> Action:
  action(Index.fit(12n, width, key))

def encode_at(width: Nat, move: Action) -> Word(width):
  Index.fit(width, 12n, encode(move))

def include(allowed: Bool, next: Position, tail: List<&2, Position>) -> List<&2, Position>:
  match allowed:
    case True{}:
      next <> tail
    case False{}:
      tail

def successors.go(depth: Nat, +width: Nat, +position: Position, keys: Finite.Table(depth, Word(width)), tail: List<&2, Position>) -> List<&2, Position>:
  match depth keys:
    case 0n +key:
      include(legal(position, action_at(width, key)), after(position, action_at(width, key)), tail)
    case 1n++rest Finite.Fork{left, right}:
      successors.go(rest, width, position, left, successors.go(rest, width, position, right, tail))

def successors(+width: Nat, position: Position) -> List<&2, Position>:
  successors.go(width, width, position, Finite.keys(width), Nil{})

def Member(+next: Position, states: List<&2, Position>) -> Type:
  match states:
    case Nil{}:
      Empty
    case head <> tail:
      {next == head : Position} | Member(next, tail)

def LegalSuccessor(+width: Nat, +position: Position, +next: Position) -> Type:
  &key: Word(width) -> Game.Truth(legal(position, action_at(width, key))) & {next == after(position, action_at(width, key)) : Position}

def from_three(material: Three.Material, board: Three.Board) -> Position:
  match board:
    case Three.Board{owner, turn, wk, bk, pc}:
      Position{turn, wk, bk, Man{owner, material, pc} <> Nil{}}

type Projection is Data:
  Single{material: Three.Material, board: Three.Board}
  NotSingle{}

def to_three(position: Position) -> Projection:
  match position:
    case Position{turn, wk, bk, Man{owner, material, pc} <> Nil{}}:
      Single{material, Three.Board{owner, turn, wk, bk, pc}}
    case _:
      NotSingle{}

def Fits(capacity: Nat, men: List<&2, Man>) -> Data:
  match capacity men:
    case _ Nil{}:
      Unit
    case 0n head <> tail:
      Empty
    case 1n+rest head <> tail:
      Fits(rest, tail)

def Bounded(capacity: Nat, position: Position) -> Data:
  match position:
    case Position{turn, wk, bk, men}:
      Fits(capacity, men)

def count(position: Position) -> Nat:
  match position:
    case Position{turn, wk, bk, men}:
      List.length(&2, Man, men)
