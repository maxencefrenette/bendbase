import Base
import ./chess_measure.bend as M
import ./position.bend as P
import ./chess.bend as Chess
import ./game.bend as Game
import ./pawnless_chess.bend as Three
import ./geometry.bend as Geometry

def and_left(+a: Bool, +b: Bool, yes: Game.Truth(a && b)) -> Game.Truth(a):
  match a b:
    case True{} True{}:
      Unit{}
    case False{} _:
      match yes:
    case True{} False{}:
      match yes:

def and_right(+a: Bool, +b: Bool, yes: Game.Truth(a && b)) -> Game.Truth(b):
  match a b:
    case True{} True{}:
      Unit{}
    case False{} _:
      match yes:
    case True{} False{}:
      match yes:

def either(-A: Type, +a: Bool, +b: Bool, yes: Game.Truth(a || b),
  left: Game.Truth(a) -> A, right: Game.Truth(b) -> A) -> A:
  match a b:
    case True{} _:
      left(Unit{})
    case False{} True{}:
      right(Unit{})
    case False{} False{}:
      match yes:

def or_left(+a: Bool, b: Bool, yes: Game.Truth(a)) -> Game.Truth(a || b):
  match a:
    case True{}:
      Unit{}
    case False{}:
      match yes:

def or_right(a: Bool, +b: Bool, yes: Game.Truth(b)) -> Game.Truth(a || b):
  match a:
    case True{}:
      Unit{}
    case False{}:
      yes

def nat_equal(+a: Nat, +b: Nat, yes: Game.Truth(Nat.is_eq(a, b))) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      match yes:
    case 1n+x 0n:
      match yes:
    case 1n+x 1n+y:
      %nat_equal(x, y, yes) : {1n+x == 1n+_ : Nat}
      {==}

def refl(n: Nat) -> M.Le(n, n):
  match n:
    case 0n:
      Unit{}
    case 1n+rest:
      refl(rest)

def weaken(+a: Nat, b: Nat, proof: M.Le(a, b)) -> M.Le(a, 1n+b):
  match a b:
    case 0n _:
      Unit{}
    case 1n+rest 0n:
      match proof:
    case 1n+x 1n+y:
      weaken(x, y, proof)

def forget(a: Nat, b: Nat, proof: M.Lt(a, b)) -> M.Le(a, b):
  match a b:
    case _ 0n:
      match proof:
    case 0n 1n+rest:
      Unit{}
    case 1n+x 1n+y:
      forget(x, y, proof)

def weak(strict: Bool, +a: Nat, +b: Nat, proof: M.Bound(strict, a, b)) -> M.Le(a, b):
  match strict:
    case False{}:
      proof
    case True{}:
      forget(a, b, proof)

def trans(a: Nat, b: Nat, c: Nat, left: M.Le(a, b), right: M.Le(b, c)) -> M.Le(a, c):
  match a b c:
    case 0n _ _:
      Unit{}
    case 1n+x 0n _:
      match left:
    case 1n+x 1n+y 0n:
      match right:
    case 1n+x 1n+y 1n+z:
      trans(x, y, z, left, right)

def prefix(extra: Nat, +a: Nat, +b: Nat, proof: M.Le(a, b)) -> M.Le(a, Nat.add(extra, b)):
  match extra:
    case 0n:
      proof
    case 1n++rest:
      weaken(a, Nat.add(rest, b), prefix(rest, a, b, proof))

def forward(+owner: Game.Player, +from: Word(6n), +dest: Word(6n), +steps: Nat,
  yes: Game.Truth(Chess.forward(owner, from, dest, 1n+steps))) -> M.Lt(M.distance(owner, dest), M.distance(owner, from)):
  %Equal.sym(Nat, M.distance(owner, from), 1n+Nat.add(steps, M.distance(owner, dest)),
    nat_equal(M.distance(owner, from), 1n+Nat.add(steps, M.distance(owner, dest)), yes)) :
    M.Lt(M.distance(owner, dest), _)
  prefix(steps, M.distance(owner, dest), M.distance(owner, dest), refl(M.distance(owner, dest)))

def pawn_paths(+owner: Game.Player, +from: Word(6n), +dest: Word(6n),
  +clear: Bool, +start: Bool, +middle: Bool, +diagonal: Bool, +capture: Bool,
  yes: Game.Truth((clear && (Chess.forward(owner, from, dest, 1n) ||
    (start && Chess.forward(owner, from, dest, 2n) && middle))) ||
    ((Chess.forward(owner, from, dest, 1n) && diagonal) && capture))) ->
  M.Lt(M.distance(owner, dest), M.distance(owner, from)):
  +one = Chess.forward(owner, from, dest, 1n)
  +two = Chess.forward(owner, from, dest, 2n)
  either(M.Lt(M.distance(owner, dest), M.distance(owner, from)),
    clear && (one || (start && two && middle)), (one && diagonal) && capture, yes,
    straight => either(M.Lt(M.distance(owner, dest), M.distance(owner, from)), one, start && two && middle,
      and_right(clear, one || (start && two && middle), straight),
      single => forward(owner, from, dest, 0n, single),
      double => forward(owner, from, dest, 1n, and_right(start, two, and_left(start && two, middle, double)))),
    diagonal_move => forward(owner, from, dest, 0n,
      and_left(one, diagonal, and_left(one && diagonal, capture, diagonal_move))))

def pawn_geometry(+owner: Game.Player, +from: Word(6n), +dest: Word(6n), +board: P.Position,
  yes: Game.Truth(Chess.pawn_geometry(owner, from, dest, board))) -> M.Lt(M.distance(owner, dest), M.distance(owner, from)):
  match board:
    case P.Position{turn, wk, bk, +pieces, ep, target}:
      pawn_paths(owner, from, dest,
        Geometry.same_file(Three.number(6n, from), Three.number(6n, dest)) && Chess.empty(board, dest),
        Chess.starting(owner, from), Chess.empty(board, Chess.shift(owner, from)),
        U32.is_eq(Geometry.distance(Geometry.file(Three.number(6n, from)), Geometry.file(Three.number(6n, dest))), 1),
        (Chess.occupied(pieces, dest) && Bool.not(Chess.friendly(pieces, owner, dest))) ||
          (ep && Chess.equal(target, dest) && Chess.empty(board, dest) &&
            Chess.pawn_at(pieces, Three.other(owner), Chess.shift(Three.other(owner), dest))), yes)

def add(+a: Nat, c: Nat, +b: Nat, +d: Nat, left: M.Le(a, c), right: M.Le(b, d)) ->
  M.Le(Nat.add(a, b), Nat.add(c, d)):
  match a c:
    case 0n c:
      prefix(c, b, d, right)
    case 1n+x 0n:
      match left:
    case 1n+x 1n+y:
      add(x, y, b, d, left, right)

def add_next(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+rest:
      %add_next(rest, b) : {1n+Nat.add(rest, 1n+b) == 1n+_ : Nat}
      {==}

def combine(+s: Bool, +t: Bool, +a: Nat, +c: Nat, +b: Nat, +d: Nat,
  left: M.Bound(s, a, c), right: M.Bound(t, b, d)) ->
  M.Bound(s || t, Nat.add(a, b), Nat.add(c, d)):
  match s t:
    case False{} False{}:
      add(a, c, b, d, left, right)
    case False{} True{}:
      %add_next(a, b) : M.Le(_, Nat.add(c, d))
      add(a, c, 1n+b, d, left, right)
    case True{} t:
      add(1n+a, c, b, d, left, weak(t, b, d, right))

def promotion_extra(promotes: Bool, +owner: Game.Player, +dest: Word(6n), choice: Three.Material) ->
  M.Le(M.extra(owner, Bool.pick(P.PieceKind, promotes, P.Piece{choice}, P.Pawn{}), dest), M.distance(owner, dest)):
  match promotes:
    case True{}:
      Unit{}
    case False{}:
      refl(M.distance(owner, dest))

def moved(+moving: Bool, +owner: Game.Player, +kind: P.PieceKind, +at: Word(6n), +dest: Word(6n), +choice: Three.Material,
  progress: M.PawnProgress(moving, owner, kind, at, dest)) ->
  M.Bound(M.moving_pawn(moving, kind), M.weight(M.moved(moving, owner, kind, at, dest, choice)), M.weight(P.Man{owner, kind, at})):
  match moving kind:
    case False{} P.Pawn{}:
      refl(M.weight(P.Man{owner, P.Pawn{}, at}))
    case False{} P.Piece{kind}:
      Unit{}
    case True{} P.Piece{kind}:
      Unit{}
    case True{} P.Pawn{}:
      trans(1n+M.extra(owner, Chess.moved_kind(True{}, owner, P.Pawn{}, dest, choice), dest),
        1n+M.distance(owner, dest), M.distance(owner, at),
        promotion_extra(Chess.promotion(owner, dest), owner, dest, choice), progress)

def drop(+man: P.Man, +after: Nat, +before: Nat, proof: M.Le(after, before)) ->
  M.Lt(after, Nat.add(M.weight(man), before)):
  match man:
    case P.Man{owner, kind, at}:
      prefix(M.extra(owner, kind, at), after, before, proof)

def keep(+remove: Bool, +moving: Bool, +strict: Bool, +old: P.Man, +next: P.Man,
  +tail: List<&2, P.Man>, +before: Nat,
  head: M.Bound(moving, M.weight(next), M.weight(old)), rest: M.Bound(strict, M.men(tail), before)) ->
  M.Bound(remove || (moving || strict), M.men(Chess.keep(remove, next, tail)), Nat.add(M.weight(old), before)):
  match remove:
    case True{}:
      drop(old, M.men(tail), before, weak(strict, M.men(tail), before, rest))
    case False{}:
      combine(moving, strict, M.weight(next), M.weight(old), M.men(tail), before, head, rest)

# One structural induction, independent of the number or kinds of pieces.
# This theorem is about the actual common move updater, including EP deletion
# and promotion, not a second implementation of chess transitions.
def update(+pieces: List<&2, P.Man>, +from: Word(6n), +dest: Word(6n), +choice: Three.Material,
  +ep: Bool, +victim: Word(6n), progress: M.Progress(pieces, from, dest)) ->
  M.Bound(M.changes(pieces, from, dest, ep, victim),
    M.men(Chess.move_men(pieces, from, dest, choice, ep, victim)), M.men(pieces)):
  match pieces progress:
    case Nil{} Unit{}:
      Unit{}
    case P.Man{+owner, +kind, +at} <> +tail Tuple{head, rest}:
      keep(Chess.equal(at, dest) || (ep && Chess.equal(at, victim)),
        M.moving_pawn(Chess.equal(at, from), kind), M.changes(tail, from, dest, ep, victim),
        P.Man{owner, kind, at}, M.moved(Chess.equal(at, from), owner, kind, at, dest, choice),
        Chess.move_men(tail, from, dest, choice, ep, victim), M.men(tail),
        moved(Chess.equal(at, from), owner, kind, at, dest, choice, head),
        update(tail, from, dest, choice, ep, victim, rest))

def capture_changes(+pieces: List<&2, P.Man>, +from: Word(6n), +dest: Word(6n), +ep: Bool, +victim: Word(6n),
  yes: Game.Truth(Chess.occupied(pieces, dest))) -> Game.Truth(M.changes(pieces, from, dest, ep, victim)):
  match pieces:
    case Nil{}:
      match yes:
    case P.Man{owner, +kind, +at} <> +tail:
      +removed = Chess.equal(at, dest) || (ep && Chess.equal(at, victim))
      +pawn = M.moving_pawn(Chess.equal(at, from), kind)
      +later = M.changes(tail, from, dest, ep, victim)
      either(Game.Truth(removed || (pawn || later)), Chess.equal(at, dest), Chess.occupied(tail, dest), yes,
        here => or_left(removed, pawn || later, or_left(Chess.equal(at, dest), ep && Chess.equal(at, victim), here)),
        there => or_right(removed, pawn || later, or_right(pawn, later, capture_changes(tail, from, dest, ep, victim, there))))

def pawn_changes(+pieces: List<&2, P.Man>, +turn: Game.Player, +from: Word(6n), +dest: Word(6n), +ep: Bool, +victim: Word(6n),
  yes: Game.Truth(Chess.pawn_at(pieces, turn, from))) -> Game.Truth(M.changes(pieces, from, dest, ep, victim)):
  match pieces:
    case Nil{}:
      match yes:
    case P.Man{+owner, P.Pawn{}, +at} <> +tail:
      +removed = Chess.equal(at, dest) || (ep && Chess.equal(at, victim))
      +moving = Chess.equal(at, from)
      +later = M.changes(tail, from, dest, ep, victim)
      either(Game.Truth(removed || (moving || later)), Three.same(owner, turn) && moving, Chess.pawn_at(tail, turn, from), yes,
        here => or_right(removed, moving || later, or_left(moving, later, and_right(Three.same(owner, turn), moving, here))),
        there => or_right(removed, moving || later, or_right(moving, later, pawn_changes(tail, turn, from, dest, ep, victim, there))))
    case P.Man{owner, P.Piece{kind}, +at} <> +tail:
      or_right(Chess.equal(at, dest) || (ep && Chess.equal(at, victim)), M.changes(tail, from, dest, ep, victim),
        pawn_changes(tail, turn, from, dest, ep, victim, yes))

def strict(+flag: Bool, +after: Nat, +before: Nat, yes: Game.Truth(flag), proof: M.Bound(flag, after, before)) -> M.Lt(after, before):
  match flag:
    case True{}:
      proof
    case False{}:
      match yes:

def after_reset(+board: P.Position, +move: Chess.Action, progress: M.MoveProgress(board, move),
  reset: Game.Truth(Chess.resets(board, move))) -> M.Lt(M.position(Chess.after(board, move)), M.position(board)):
  match board move:
    case P.Position{+turn, wk, bk, +pieces, ep, target} Chess.Action{+from, +dest, +choice}:
      +en_passant = Chess.ep_move(board, move)
      +victim = Chess.shift(Three.other(turn), dest)
      strict(M.changes(pieces, from, dest, en_passant, victim),
        M.men(Chess.move_men(pieces, from, dest, choice, en_passant, victim)), M.men(pieces),
        either(Game.Truth(M.changes(pieces, from, dest, en_passant, victim)), Chess.pawn_at(pieces, turn, from), Chess.occupied(pieces, dest), reset,
          pawn => pawn_changes(pieces, turn, from, dest, en_passant, victim, pawn),
          capture => capture_changes(pieces, from, dest, en_passant, victim, capture)),
        update(pieces, from, dest, choice, en_passant, victim, progress))
