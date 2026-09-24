import Base
import ./position.bend as P
import ./game.bend as Game
import ./pawnless_chess.bend as Three
import ./material_chess.bend as Material
import ./geometry.bend as Geometry
import ./pawnless_index.bend as Index
import ./finite_table.bend as Finite

# Common no-castling move rules. Promotion choice is ignored on non-promoting
# moves; the four redundant encodings do not change the set of successors.
type Action is Data:
  Action{from: Word(6n), dest: Word(6n), promotion: Three.Material}

def equal(a: Word(6n), b: Word(6n)) -> Bool:
  Material.equal(a, b)

def bits(n: Nat, +value: U32) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n++rest:
      WCon{U32.is_ne(U32.and(U32.shrn(value, rest), 1), 0), bits(rest, value)}

def occupied(men: List<&2, P.Man>, +square: Word(6n)) -> Bool:
  match men:
    case Nil{}:
      False{}
    case P.Man{owner, kind, at} <> tail:
      equal(at, square) || occupied(tail, square)

def friendly(men: List<&2, P.Man>, +player: Game.Player, +square: Word(6n)) -> Bool:
  match men:
    case Nil{}:
      False{}
    case P.Man{owner, kind, at} <> tail:
      (Three.same(owner, player) && equal(at, square)) || friendly(tail, player, square)

def pawn_at(men: List<&2, P.Man>, +player: Game.Player, +square: Word(6n)) -> Bool:
  match men:
    case Nil{}:
      False{}
    case P.Man{owner, P.Pawn{}, at} <> tail:
      (Three.same(owner, player) && equal(at, square)) || pawn_at(tail, player, square)
    case P.Man{owner, P.Piece{kind}, at} <> tail:
      pawn_at(tail, player, square)

def distinct(men: List<&2, P.Man>, +wk: Word(6n), +bk: Word(6n)) -> Bool:
  match men:
    case Nil{}:
      True{}
    case P.Man{owner, kind, +at} <> +tail:
      Bool.not(equal(at, wk)) && Bool.not(equal(at, bk)) &&
        Bool.not(occupied(tail, at)) && distinct(tail, wk, bk)

def pawn_rank(kind: P.PieceKind, square: Word(6n)) -> Bool:
  match kind:
    case P.Piece{kind}:
      True{}
    case P.Pawn{}:
      +rank = Geometry.rank(Three.number(6n, square))
      U32.is_lt(0, rank) && U32.is_lt(rank, 7)

def ranks(men: List<&2, P.Man>) -> Bool:
  match men:
    case Nil{}:
      True{}
    case P.Man{owner, kind, at} <> tail:
      pawn_rank(kind, at) && ranks(tail)

def clear(men: List<&2, P.Man>, +from: Word(6n), +dest: Word(6n)) -> Bool:
  match men:
    case Nil{}:
      True{}
    case P.Man{owner, kind, at} <> tail:
      Bool.not(Geometry.on_segment(Three.number(6n, from), Three.number(6n, dest), Three.number(6n, at))) && clear(tail, from, dest)

def forward(owner: Game.Player, from: U32, dest: U32, steps: U32) -> Bool:
  match owner:
    case Game.White{}:
      U32.is_eq(Geometry.rank(dest), (Geometry.rank(from) + steps : U32))
    case Game.Black{}:
      U32.is_eq(Geometry.rank(from), (Geometry.rank(dest) + steps : U32))

def king(position: P.Position, player: Game.Player) -> Word(6n):
  match position player:
    case P.Position{turn, wk, bk, men, ep, target} Game.White{}:
      wk
    case P.Position{turn, wk, bk, men, ep, target} Game.Black{}:
      bk

def attacks(owner: Game.Player, kind: P.PieceKind, +from: Word(6n), +dest: Word(6n), position: P.Position) -> Bool:
  match kind position:
    case P.Pawn{} _:
      forward(owner, Three.number(6n, from), Three.number(6n, dest), 1) &&
        U32.is_eq(Geometry.distance(Geometry.file(Three.number(6n, from)), Geometry.file(Three.number(6n, dest))), 1)
    case P.Piece{+kind} P.Position{turn, wk, bk, men, ep, target}:
      Geometry.piece_step(Three.kind(kind), Three.number(6n, from), Three.number(6n, dest), Three.number(6n, wk), Three.number(6n, bk)) &&
        (U32.is_eq(Three.kind(kind), 3) || clear(men, from, dest))

def threatened(men: List<&2, P.Man>, +position: P.Position, +player: Game.Player, +target: Word(6n)) -> Bool:
  match men:
    case Nil{}:
      False{}
    case P.Man{+owner, kind, at} <> tail:
      (Bool.not(Three.same(owner, player)) && attacks(owner, kind, at, target, position)) || threatened(tail, position, player, target)

def checked(+position: P.Position, +player: Game.Player) -> Bool:
  match position:
    case P.Position{turn, +wk, +bk, men, ep, target}:
      Geometry.kings_touch(Three.number(6n, wk), Three.number(6n, bk)) || threatened(men, position, player, king(position, player))

def valid_plain(+position: P.Position) -> Bool:
  match position:
    case P.Position{+turn, +wk, +bk, +men, ep, target}:
      Bool.not(equal(wk, bk)) && distinct(men, wk, bk) && ranks(men) &&
        Bool.not(checked(position, Three.other(turn)))

def empty(position: P.Position, +square: Word(6n)) -> Bool:
  match position:
    case P.Position{turn, wk, bk, men, ep, target}:
      Bool.not(equal(wk, square)) && Bool.not(equal(bk, square)) && Bool.not(occupied(men, square))

def shift(owner: Game.Player, square: Word(6n)) -> Word(6n):
  match owner:
    case Game.White{}:
      bits(6n, (Three.number(6n, square) + 8 : U32))
    case Game.Black{}:
      bits(6n, (Three.number(6n, square) - 8 : U32))

def relocate(men: List<&2, P.Man>, +from: Word(6n), +dest: Word(6n)) -> List<&2, P.Man>:
  match men:
    case Nil{}:
      Nil{}
    case P.Man{owner, kind, at} <> tail:
      P.Man{owner, kind, Material.move_square(at, from, dest)} <> relocate(tail, from, dest)

# Reconstruct the immediately preceding double push for asserted EP rights.
# Both traversed squares were empty, the predecessor was valid, and the
# mover's king is safe afterward. Being in check BEFORE the double push is
# allowed: the push can block that check. No repetition/castling history.
def previous(+position: P.Position) -> P.Position:
  match position:
    case P.Position{+turn, wk, bk, men, ep, +target}:
      P.Position{Three.other(turn), wk, bk,
        relocate(men, shift(Three.other(turn), target), shift(turn, target)), False{}, Word.zero(6n)}

def ep_rank(turn: Game.Player, target: Word(6n)) -> Bool:
  match turn:
    case Game.White{}:
      U32.is_eq(Geometry.rank(Three.number(6n, target)), 5)
    case Game.Black{}:
      U32.is_eq(Geometry.rank(Three.number(6n, target)), 2)

def valid_rights(+position: P.Position) -> Bool:
  match position:
    case P.Position{turn, wk, bk, men, False{}, target}:
      True{}
    case P.Position{+turn, wk, bk, men, True{}, +target}:
      ep_rank(turn, target) && empty(position, target) && empty(position, shift(turn, target)) &&
        pawn_at(men, Three.other(turn), shift(Three.other(turn), target)) && valid_plain(previous(position))

def valid(+position: P.Position) -> Bool:
  valid_plain(position) && valid_rights(position)

def pawn_move(position: P.Position, action: Action) -> Bool:
  match position action:
    case P.Position{turn, wk, bk, men, ep, target} Action{from, dest, promotion}:
      pawn_at(men, turn, from)

def ep_move(+position: P.Position, +action: Action) -> Bool:
  match position action:
    case P.Position{turn, wk, bk, men, ep, target} Action{from, +dest, promotion}:
      ep && pawn_move(position, action) && equal(target, dest) && empty(position, dest)

def double_move(+position: P.Position, +action: Action) -> Bool:
  match action:
    case Action{from, dest, promotion}:
      pawn_move(position, action) && U32.is_eq(Geometry.distance(Geometry.rank(Three.number(6n, from)), Geometry.rank(Three.number(6n, dest))), 2)

def promotion(owner: Game.Player, square: Word(6n)) -> Bool:
  match owner:
    case Game.White{}:
      U32.is_eq(Geometry.rank(Three.number(6n, square)), 7)
    case Game.Black{}:
      U32.is_eq(Geometry.rank(Three.number(6n, square)), 0)

def moved_kind(moving: Bool, owner: Game.Player, kind: P.PieceKind, dest: Word(6n), choice: Three.Material) -> P.PieceKind:
  match moving kind:
    case True{} P.Pawn{}:
      Bool.pick(P.PieceKind, promotion(owner, dest), P.Piece{choice}, P.Pawn{})
    case _ kind:
      kind

def keep(remove: Bool, man: P.Man, tail: List<&2, P.Man>) -> List<&2, P.Man>:
  match remove:
    case True{}:
      tail
    case False{}:
      man <> tail

def move_men(men: List<&2, P.Man>, +from: Word(6n), +dest: Word(6n), +choice: Three.Material,
  +ep: Bool, +victim: Word(6n)) -> List<&2, P.Man>:
  match men:
    case Nil{}:
      Nil{}
    case P.Man{+owner, kind, +at} <> tail:
      keep(equal(at, dest) || (ep && equal(at, victim)),
        P.Man{owner, moved_kind(equal(at, from), owner, kind, dest, choice), Material.move_square(at, from, dest)},
        move_men(tail, from, dest, choice, ep, victim))

def after(+position: P.Position, +action: Action) -> P.Position:
  match position action:
    case P.Position{+turn, wk, bk, men, ep, target} Action{+from, +dest, choice}:
      +double = double_move(position, action)
      P.Position{Three.other(turn), Material.move_square(wk, from, dest), Material.move_square(bk, from, dest),
        move_men(men, from, dest, choice, ep_move(position, action), shift(Three.other(turn), dest)),
        double, Bool.pick(Word(6n), double, shift(turn, from), Word.zero(6n))}

def starting(owner: Game.Player, from: Word(6n)) -> Bool:
  match owner:
    case Game.White{}:
      U32.is_eq(Geometry.rank(Three.number(6n, from)), 1)
    case Game.Black{}:
      U32.is_eq(Geometry.rank(Three.number(6n, from)), 6)

def pawn_geometry(+owner: Game.Player, +from: Word(6n), +dest: Word(6n), +position: P.Position) -> Bool:
  match position:
    case P.Position{turn, wk, bk, +men, ep, target}:
      (Geometry.same_file(Three.number(6n, from), Three.number(6n, dest)) && empty(position, dest) &&
        (forward(owner, Three.number(6n, from), Three.number(6n, dest), 1) ||
         (starting(owner, from) && forward(owner, Three.number(6n, from), Three.number(6n, dest), 2) && empty(position, shift(owner, from))))) ||
      (attacks(owner, P.Pawn{}, from, dest, position) &&
        ((occupied(men, dest) && Bool.not(friendly(men, owner, dest))) ||
         (ep && equal(target, dest) && empty(position, dest) && pawn_at(men, Three.other(owner), shift(Three.other(owner), dest)))))

def geometry(owner: Game.Player, kind: P.PieceKind, from: Word(6n), dest: Word(6n), position: P.Position) -> Bool:
  match kind:
    case P.Pawn{}:
      pawn_geometry(owner, from, dest, position)
    case P.Piece{kind}:
      attacks(owner, P.Piece{kind}, from, dest, position)

def piece_move(men: List<&2, P.Man>, +position: P.Position, +turn: Game.Player, +from: Word(6n), +dest: Word(6n)) -> Bool:
  match men:
    case Nil{}:
      False{}
    case P.Man{+owner, kind, +at} <> tail:
      (Three.same(owner, turn) && equal(at, from) && geometry(owner, kind, from, dest, position)) || piece_move(tail, position, turn, from, dest)

def pseudo(+position: P.Position, action: Action) -> Bool:
  match position action:
    case P.Position{+turn, +wk, +bk, +men, ep, target} Action{+from, +dest, choice}:
      Bool.not(equal(dest, wk)) && Bool.not(equal(dest, bk)) && Bool.not(friendly(men, turn, dest)) &&
        ((equal(from, king(position, turn)) && Geometry.king_step(Three.number(6n, from), Three.number(6n, dest))) ||
          piece_move(men, position, turn, from, dest))

def legal(+position: P.Position, +action: Action) -> Bool:
  (valid(position) && pseudo(position, action)) && valid(after(position, action))

# This classification is shared by every material configuration. En passant
# resets because it is a pawn move, even though its destination is empty.
def resets(+position: P.Position, +action: Action) -> Bool:
  match position action:
    case P.Position{turn, wk, bk, men, ep, target} Action{from, dest, choice}:
      pawn_move(position, action) || occupied(men, dest)

def action_parts(kind: Three.Material, move: Material.Action) -> Action:
  match move:
    case Material.Action{from, dest}:
      Action{from, dest, kind}

def action(key: Word(14n)) -> Action:
  match key:
    case WCon{False{}, WCon{False{}, tail}}:
      action_parts(Three.Queen{}, Material.action(tail))
    case WCon{False{}, WCon{True{}, tail}}:
      action_parts(Three.Rook{}, Material.action(tail))
    case WCon{True{}, WCon{False{}, tail}}:
      action_parts(Three.Bishop{}, Material.action(tail))
    case WCon{True{}, WCon{True{}, tail}}:
      action_parts(Three.Knight{}, Material.action(tail))

def encode(move: Action) -> Word(14n):
  match move:
    case Action{from, dest, Three.Queen{}}:
      WCon{False{}, WCon{False{}, Material.encode(Material.Action{from, dest})}}
    case Action{from, dest, Three.Rook{}}:
      WCon{False{}, WCon{True{}, Material.encode(Material.Action{from, dest})}}
    case Action{from, dest, Three.Bishop{}}:
      WCon{True{}, WCon{False{}, Material.encode(Material.Action{from, dest})}}
    case Action{from, dest, Three.Knight{}}:
      WCon{True{}, WCon{True{}, Material.encode(Material.Action{from, dest})}}

def action_at(+width: Nat, key: Word(width)) -> Action:
  action(Index.fit(14n, width, key))

def encode_at(width: Nat, move: Action) -> Word(width):
  Index.fit(width, 14n, encode(move))

def include(allowed: Bool, next: P.Position, tail: List<&2, P.Position>) -> List<&2, P.Position>:
  match allowed:
    case True{}:
      next <> tail
    case False{}:
      tail

def successors.go(depth: Nat, +width: Nat, +position: P.Position,
  keys: Finite.Table(depth, Word(width)), tail: List<&2, P.Position>) -> List<&2, P.Position>:
  match depth keys:
    case 0n +key:
      include(legal(position, action_at(width, key)), after(position, action_at(width, key)), tail)
    case 1n++rest Finite.Fork{left, right}:
      successors.go(rest, width, position, left, successors.go(rest, width, position, right, tail))

def successors(+width: Nat, position: P.Position) -> List<&2, P.Position>:
  successors.go(width, width, position, Finite.keys(width), Nil{})

def Member(+next: P.Position, states: List<&2, P.Position>) -> Type:
  match states:
    case Nil{}:
      Empty
    case head <> tail:
      {next == head : P.Position} | Member(next, tail)

def LegalSuccessor(+width: Nat, +position: P.Position, +next: P.Position) -> Type:
  &key: Word(width) -> Game.Truth(legal(position, action_at(width, key))) & {next == after(position, action_at(width, key)) : P.Position}

def color(square: Word(6n)) -> U32:
  +number = Three.number(6n, square)
  U32.and((Geometry.file(number) + Geometry.rank(number) : U32), 1)

def bishops(men: List<&2, P.Man>, +shade: U32) -> Bool:
  match men:
    case Nil{}:
      True{}
    case P.Man{owner, P.Piece{Three.Bishop{}}, square} <> tail:
      U32.is_eq(color(square), shade) && bishops(tail, shade)
    case _:
      False{}

def insufficient(men: List<&2, P.Man>) -> Bool:
  match men:
    case Nil{}:
      True{}
    case P.Man{owner, P.Piece{Three.Knight{}}, square} <> Nil{}:
      True{}
    case P.Man{owner, P.Piece{Three.Bishop{}}, square} <> tail:
      bishops(tail, color(square))
    case _:
      False{}

type View is Data:
  Terminal{result: Game.Outcome}
  Play{turn: Game.Player, children: List<&2, P.Position>}

def view.moves(+position: P.Position, children: List<&2, P.Position>) -> View:
  match position children:
    case P.Position{+turn, wk, bk, men, ep, target} Nil{}:
      Terminal{Three.mate(checked(position, turn), turn)}
    case P.Position{turn, wk, bk, men, ep, target} head <> tail:
      Play{turn, head <> tail}

def view.live(live: Bool, width: Nat, +position: P.Position) -> View:
  match live:
    case False{}:
      Terminal{Game.Draw{}}
    case True{}:
      view.moves(position, successors(width, position))

def view(width: Nat, +position: P.Position) -> View:
  match position:
    case P.Position{turn, wk, bk, men, ep, target}:
      view.live(valid(position) && Bool.not(insufficient(men)), width, position)

# Terminal detection precedes the 100-halfmove boundary: an already delivered
# mate is still a win. A live node with no halfmoves remaining is a draw.
def boundary(view: View) -> Game.Outcome:
  match view:
    case Terminal{result}:
      result
    case Play{turn, children}:
      Game.Draw{}
