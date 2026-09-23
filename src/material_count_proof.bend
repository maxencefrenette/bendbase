import Base
import ./game.bend as Game
import ./material_chess.bend as Chess

def weaken(capacity: Nat, +men: List<&2, Chess.Man>, bounded: Chess.Fits(capacity, men)) -> Chess.Fits(1n+capacity, men):
  match capacity men:
    case 0n Nil{}:
      Unit{}
    case 0n head <> tail:
      match bounded:
    case 1n+rest Nil{}:
      Unit{}
    case 1n+rest head <> tail:
      weaken(rest, tail, bounded)

def keep_bounded(+capacity: Nat, +remove: Bool, +man: Chess.Man, +tail: List<&2, Chess.Man>, bounded: Chess.Fits(capacity, tail)) ->
  Chess.Fits(1n+capacity, Chess.keep(remove, man, tail)):
  match remove:
    case True{}:
      weaken(capacity, tail, bounded)
    case False{}:
      bounded

def move_bounded(capacity: Nat, +men: List<&2, Chess.Man>, +from: Word(6n), +dest: Word(6n), bounded: Chess.Fits(capacity, men)) ->
  Chess.Fits(capacity, Chess.move_men(men, from, dest)):
  match capacity men:
    case 0n Nil{}:
      Unit{}
    case 0n head <> tail:
      match bounded:
    case 1n+rest Nil{}:
      Unit{}
    case 1n++rest Chess.Man{+owner, +kind, +at} <> +tail:
      keep_bounded(rest, Chess.equal(at, dest), Chess.Man{owner, kind, Chess.move_square(at, from, dest)},
        Chess.move_men(tail, from, dest), move_bounded(rest, tail, from, dest, bounded))

def after_bounded(+capacity: Nat, +position: Chess.Position, +move: Chess.Action, bounded: Chess.Bounded(capacity, position)) ->
  Chess.Bounded(capacity, Chess.after(position, move)):
  match position move:
    case Chess.Position{turn, wk, bk, men} Chess.Action{from, dest}:
      move_bounded(capacity, men, from, dest, bounded)

def only_capture(+remove: Bool, +man: Chess.Man, captured: Game.Truth(remove || False{})) ->
  Chess.Fits(0n, Chess.keep(remove, man, Nil{})):
  match remove:
    case True{}:
      Unit{}
    case False{}:
      match captured:

def capture_keep(+capacity: Nat, +remove: Bool, +man: Chess.Man, +tail: List<&2, Chess.Man>, +found: Bool,
  bounded: Chess.Fits(1n+capacity, tail), captured: Game.Truth(remove || found),
  later: Game.Truth(found) -> Chess.Fits(capacity, tail)) -> Chess.Fits(1n+capacity, Chess.keep(remove, man, tail)):
  match remove:
    case True{}:
      bounded
    case False{}:
      later(captured)

# A capture decreases the number of non-kings, structurally. This justifies
# the four -> three -> bare-kings clock-reset ordering, without a ply cutoff.
def move_captured(capacity: Nat, +men: List<&2, Chess.Man>, +from: Word(6n), +dest: Word(6n),
  +bounded: Chess.Fits(1n+capacity, men), captured: Game.Truth(Chess.occupied(men, dest))) ->
  Chess.Fits(capacity, Chess.move_men(men, from, dest)):
  match capacity men:
    case 0n Nil{}:
      match captured:
    case 1n+rest Nil{}:
      match captured:
    case 0n Chess.Man{owner, kind, +at} <> Nil{}:
      only_capture(Chess.equal(at, dest), Chess.Man{owner, kind, Chess.move_square(at, from, dest)}, captured)
    case 0n head <> next <> tail:
      match bounded:
    case 1n++rest Chess.Man{owner, kind, +at} <> +tail:
      capture_keep(rest, Chess.equal(at, dest), Chess.Man{owner, kind, Chess.move_square(at, from, dest)},
        Chess.move_men(tail, from, dest), Chess.occupied(tail, dest),
        move_bounded(1n+rest, tail, from, dest, bounded), captured,
        later => move_captured(rest, tail, from, dest, bounded, later))

def after_captured(+capacity: Nat, +position: Chess.Position, +move: Chess.Action,
  bounded: Chess.Bounded(1n+capacity, position), captured: Game.Truth(Chess.capture(position, move))) ->
  Chess.Bounded(capacity, Chess.after(position, move)):
  match position move:
    case Chess.Position{turn, wk, bk, men} Chess.Action{from, dest}:
      move_captured(capacity, men, from, dest, bounded, captured)

def not_or_left(+a: Bool, +b: Bool, no: Game.Truth(Bool.not(a || b))) -> Game.Truth(Bool.not(a)):
  match a b:
    case False{} False{}:
      Unit{}
    case False{} True{}:
      match no:
    case True{} _:
      match no:

def not_or_right(+a: Bool, +b: Bool, no: Game.Truth(Bool.not(a || b))) -> Game.Truth(Bool.not(b)):
  match a b:
    case False{} False{}:
      Unit{}
    case False{} True{}:
      match no:
    case True{} _:
      match no:

def keep_length(+remove: Bool, +man: Chess.Man, +tail: List<&2, Chess.Man>, no: Game.Truth(Bool.not(remove))) ->
  {List.length(&2, Chess.Man, Chess.keep(remove, man, tail)) == 1n+List.length(&2, Chess.Man, tail) : Nat}:
  match remove:
    case False{}:
      {==}
    case True{}:
      match no:

def move_quiet(+men: List<&2, Chess.Man>, +from: Word(6n), +dest: Word(6n),
  +no: Game.Truth(Bool.not(Chess.occupied(men, dest)))) ->
  {List.length(&2, Chess.Man, Chess.move_men(men, from, dest)) == List.length(&2, Chess.Man, men) : Nat}:
  match men:
    case Nil{}:
      {==}
    case Chess.Man{owner, kind, +at} <> +tail:
      Equal.trans(Nat, List.length(&2, Chess.Man, Chess.move_men(men, from, dest)),
        1n+List.length(&2, Chess.Man, Chess.move_men(tail, from, dest)), 1n+List.length(&2, Chess.Man, tail),
        keep_length(Chess.equal(at, dest), Chess.Man{owner, kind, Chess.move_square(at, from, dest)},
          Chess.move_men(tail, from, dest), not_or_left(Chess.equal(at, dest), Chess.occupied(tail, dest), no)),
        Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Chess.Man, Chess.move_men(tail, from, dest)),
          List.length(&2, Chess.Man, tail),
          move_quiet(tail, from, dest, not_or_right(Chess.equal(at, dest), Chess.occupied(tail, dest), no))))

def after_quiet(+position: Chess.Position, +move: Chess.Action,
  no: Game.Truth(Bool.not(Chess.capture(position, move)))) ->
  {Chess.count(Chess.after(position, move)) == Chess.count(position) : Nat}:
  match position move:
    case Chess.Position{turn, wk, bk, men} Chess.Action{from, dest}:
      move_quiet(men, from, dest, no)
