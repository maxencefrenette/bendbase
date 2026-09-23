import Base
import ./game.bend as Game
import ./pawnless_chess.bend as Three
import ./material_chess.bend as Chess
import ./four_chess.bend as Rules
import ./four_index.bend as Index
import ./pawnless_generator.bend as Gen
import ./finite_table.bend as Finite

type Both<-A: Data, -B: Data> is Data:
  Both{head: A, tail: B}

# The cache invariant: quiet moves preserve the ordered kinds and owners.
# In a double-piece scope any single survivor is routed to its own lower table.
def SingleMen(men: List<&2, Chess.Man>, kind: Three.Material) -> Data:
  match men:
    case Nil{}:
      Unit
    case Chess.Man{owner, actual, at} <> Nil{}:
      {actual == kind : Three.Material}
    case _:
      Empty

def DoubleMen(men: List<&2, Chess.Man>, material: Index.Material) -> Data:
  match men material:
    case Nil{} _:
      Unit
    case man <> Nil{} _:
      Unit
    case Chess.Man{a, first, x} <> Chess.Man{b, second, y} <> Nil{} Index.Material{one, two, opposed}:
      Both<{first == one : Three.Material}, Both<{second == two : Three.Material},
        {b == Bool.pick(Game.Player, opposed, Three.other(a), a) : Game.Player}>>
    case _ _:
      Empty

def Men(men: List<&2, Chess.Man>, scope: Gen.Scope) -> Data:
  match scope:
    case Gen.Single{kind}:
      SingleMen(men, kind)
    case Gen.Double{material}:
      DoubleMen(men, material)

def Holds(scope: Gen.Scope, position: Chess.Position) -> Data:
  match position:
    case Chess.Position{turn, wk, bk, men}:
      Men(men, scope)

def All(scope: Gen.Scope, positions: List<&2, Chess.Position>) -> Data:
  match positions:
    case Nil{}:
      Unit
    case head <> tail:
      Both<Holds(scope, head), All(scope, tail)>

def keep_one(+remove: Bool, +scope: Gen.Scope, +man: Chess.Man,
  shape: Men(man <> Nil{}, scope)) -> Men(Chess.keep(remove, man, Nil{}), scope):
  match remove scope:
    case True{} Gen.Single{kind}:
      Unit{}
    case True{} Gen.Double{material}:
      Unit{}
    case False{} _:
      shape

def one_double(+man: Chess.Man, material: Index.Material) -> Men(man <> Nil{}, Gen.Double{material}):
  match man:
    case Chess.Man{owner, kind, square}:
      Unit{}

def keep_two(+first: Bool, +second: Bool, +material: Index.Material, +a: Chess.Man, +b: Chess.Man,
  shape: Men(a <> b <> Nil{}, Gen.Double{material})) ->
  Men(Chess.keep(first, a, Chess.keep(second, b, Nil{})), Gen.Double{material}):
  match first second:
    case True{} True{}:
      Unit{}
    case True{} False{}:
      one_double(b, material)
    case False{} True{}:
      one_double(a, material)
    case False{} False{}:
      shape

def moved(+men: List<&2, Chess.Man>, +scope: Gen.Scope, +from: Word(6n), +dest: Word(6n),
  shape: Men(men, scope)) -> Men(Chess.move_men(men, from, dest), scope):
  match men scope:
    case Nil{} Gen.Single{kind}:
      Unit{}
    case Nil{} Gen.Double{material}:
      Unit{}
    case Chess.Man{owner, kind, +at} <> Nil{} Gen.Single{expected}:
      keep_one(Chess.equal(at, dest), scope, Chess.Man{owner, kind, Chess.move_square(at, from, dest)}, shape)
    case Chess.Man{owner, kind, +at} <> Nil{} Gen.Double{material}:
      keep_one(Chess.equal(at, dest), scope, Chess.Man{owner, kind, Chess.move_square(at, from, dest)}, shape)
    case Chess.Man{a, first, +x} <> Chess.Man{b, second, +y} <> Nil{} Gen.Double{Index.Material{one, two, opposed}}:
      keep_two(Chess.equal(x, dest), Chess.equal(y, dest), Index.Material{one, two, opposed},
        Chess.Man{a, first, Chess.move_square(x, from, dest)}, Chess.Man{b, second, Chess.move_square(y, from, dest)}, shape)
    case Chess.Man{oa, ka, xa} <> b <> tail Gen.Single{kind}:
      match shape:
    case Chess.Man{oa, ka, xa} <> Chess.Man{ob, kb, xb} <> c <> tail Gen.Double{Index.Material{one, two, opposed}}:
      match shape:

def after(+scope: Gen.Scope, +position: Chess.Position, +move: Chess.Action,
  shape: Holds(scope, position)) -> Holds(scope, Chess.after(position, move)):
  match position move:
    case Chess.Position{turn, wk, bk, men} Chess.Action{from, dest}:
      moved(men, scope, from, dest, shape)

def include(+allowed: Bool, +scope: Gen.Scope, +next: Chess.Position, +tail: List<&2, Chess.Position>,
  head: Holds(scope, next), rest: All(scope, tail)) -> All(scope, Chess.include(allowed, next, tail)):
  match allowed:
    case True{}:
      Both{head, rest}
    case False{}:
      rest

def scan(depth: Nat, +width: Nat, +scope: Gen.Scope, +position: Chess.Position,
  +keys: Finite.Table(depth, Word(width)), +tail: List<&2, Chess.Position>,
  +shape: Holds(scope, position), rest: All(scope, tail)) ->
  All(scope, Chess.successors.go(depth, width, position, keys, tail)):
  match depth keys:
    case 0n +key:
      include(Chess.legal(position, Chess.action_at(width, key)), scope, Chess.after(position, Chess.action_at(width, key)), tail,
        after(scope, position, Chess.action_at(width, key), shape), rest)
    case 1n++n Finite.Fork{+left, +right}:
      scan(n, width, scope, position, left, Chess.successors.go(n, width, position, right, tail), shape,
        scan(n, width, scope, position, right, tail, shape, rest))

def view_moves(+scope: Gen.Scope, +position: Chess.Position, +children: List<&2, Chess.Position>,
  all: All(scope, children)) -> All(scope, Rules.children(Rules.view.moves(position, children))):
  match position children:
    case Chess.Position{turn, wk, bk, men} Nil{}:
      Unit{}
    case Chess.Position{turn, wk, bk, men} head <> tail:
      all

def view_live(+live: Bool, +moves: Nat, +scope: Gen.Scope, +position: Chess.Position,
  shape: Holds(scope, position)) -> All(scope, Rules.children(Rules.view.live(live, moves, position))):
  match live:
    case False{}:
      Unit{}
    case True{}:
      view_moves(scope, position, Chess.successors(moves, position),
        scan(moves, moves, scope, position, Finite.keys(moves), Nil{}, shape, Unit{}))

def children(+moves: Nat, +scope: Gen.Scope, +position: Chess.Position, shape: Holds(scope, position)) ->
  All(scope, Rules.children(Rules.view(moves, position))):
  match position:
    case Chess.Position{turn, wk, bk, +men}:
      view_live(Chess.valid(position) && Bool.not(Rules.insufficient(men)), moves, scope, position, shape)
