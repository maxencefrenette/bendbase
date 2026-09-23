import Base
import ./game.bend as Game
import ./pawnless_chess.bend as Three
import ./pawn_chess.bend as Pawn
import ./material_chess.bend as Material
import ./one_pawn_chess.bend as One
import ./geometry.bend as Geometry
import ./finite_table.bend as Finite
import ./pawnless_index.bend as Index

type Seed is Data:
  Seed{owner: Game.Player, file: Word(3n)}

# Identify the pawn which made the immediately preceding double push.
# Rights are transient calculation state, not part of the stored table key.
type Rights is Data:
  NoEP{}
  FirstEP{}
  SecondEP{}

type Position is Data:
  Position{turn: Game.Player, wk: Word(6n), bk: Word(6n), first: Seed, second: Seed, ep: Rights}

type Action is Data:
  King{dest: Word(6n)}
  Step{second: Bool, file: Word(3n)}
  Double{second: Bool}
  Promote{second: Bool, file: Word(3n), kind: Three.Material}
  EnPassant{second: Bool}
  Unused{}

type Edge is Data:
  Quiet{position: Position}
  FirstPush{position: Position}
  FirstDouble{position: Position}
  SecondPush{position: Position}
  SecondDouble{position: Position}
  KPK{board: Three.Board}
  Promoted{advance: Nat, position: One.Position}
  Pawnless{position: Material.Position}

def turn(position: Position) -> Game.Player:
  match position:
    case Position{turn, wk, bk, first, second, ep}:
      turn

def seed(second: Bool, position: Position) -> Seed:
  match second position:
    case False{} Position{turn, wk, bk, first, second, ep}:
      first
    case True{} Position{turn, wk, bk, first, second, ep}:
      second

def owner(seed: Seed) -> Game.Player:
  match seed:
    case Seed{owner, file}:
      owner

def file_of(seed: Seed) -> Word(3n):
  match seed:
    case Seed{owner, file}:
      file

def square(advance: Nat, seed: Seed) -> Word(6n):
  match seed:
    case Seed{owner, file}:
      Pawn.square(Pawn.rank(advance, owner), file)

def pawn_position(second: Bool, position: Position) -> Pawn.Position:
  match second position:
    case False{} Position{turn, wk, bk, Seed{owner, file}, second, ep}:
      Pawn.Position{owner, turn, wk, bk, file}
    case True{} Position{turn, wk, bk, first, Seed{owner, file}, ep}:
      Pawn.Position{owner, turn, wk, bk, file}

def king(player: Game.Player, position: Position) -> Word(6n):
  match player position:
    case Game.White{} Position{turn, wk, bk, first, second, ep}:
      wk
    case Game.Black{} Position{turn, wk, bk, first, second, ep}:
      bk

def checked(+a: Nat, +b: Nat, +position: Position, +player: Game.Player) -> Bool:
  match position:
    case Position{turn, wk, bk, first, second, ep}:
      +target = king(player, position)
      Geometry.kings_touch(Three.number(6n, wk), Three.number(6n, bk)) ||
        (Bool.not(Three.same(owner(first), player)) && Pawn.attacks(a, pawn_position(False{}, position), target)) ||
        (Bool.not(Three.same(owner(second), player)) && Pawn.attacks(b, pawn_position(True{}, position), target))

def valid_plain(+a: Nat, +b: Nat, +position: Position) -> Bool:
  match position:
    case Position{+turn, +wk, +bk, +first, +second, ep}:
      Pawn.on_board(a) && Pawn.on_board(b) && Bool.not(Material.equal(wk, bk)) &&
        Material.distinct(Material.Man{owner(first), Three.Queen{}, square(a, first)} <>
          Material.Man{owner(second), Three.Queen{}, square(b, second)} <> Nil{}, wk, bk) &&
        Bool.not(Geometry.kings_touch(Three.number(6n, wk), Three.number(6n, bk))) &&
        Bool.not(checked(a, b, position, Three.other(turn)))

def empty(+a: Nat, +b: Nat, position: Position, +dest: Word(6n)) -> Bool:
  match position:
    case Position{turn, wk, bk, first, second, ep}:
      Bool.not(Material.equal(dest, wk)) && Bool.not(Material.equal(dest, bk)) &&
        Bool.not(Material.equal(dest, square(a, first))) && Bool.not(Material.equal(dest, square(b, second)))

def previous(position: Position) -> Position:
  match position:
    case Position{turn, wk, bk, first, second, ep}:
      Position{Three.other(turn), wk, bk, first, second, NoEP{}}

# Reconstruct the only possible predecessor for the asserted EP right. The
# pawn was on its starting rank, both traversed squares were free, and the
# predecessor and current placement meet the king-safety rules.
def valid_rights(+a: Nat, +b: Nat, +position: Position) -> Bool:
  match a b position:
    case _ _ Position{turn, wk, bk, first, second, NoEP{}}:
      True{}
    case 4n _ Position{+turn, wk, bk, +first, second, FirstEP{}}:
      Bool.not(Three.same(owner(first), turn)) && valid_plain(6n, b, previous(position)) &&
        empty(6n, b, position, square(5n, first))
    case _ 4n Position{+turn, wk, bk, first, +second, SecondEP{}}:
      Bool.not(Three.same(owner(second), turn)) && valid_plain(a, 6n, previous(position)) &&
        empty(a, 6n, position, square(5n, second))
    case _ _ _:
      False{}

def valid(+a: Nat, +b: Nat, +position: Position) -> Bool:
  valid_plain(a, b, position) && valid_rights(a, b, position)

def after_king(position: Position, dest: Word(6n)) -> Position:
  match position:
    case Position{Game.White{}, wk, bk, first, second, ep}:
      Position{Game.Black{}, dest, bk, first, second, NoEP{}}
    case Position{Game.Black{}, wk, bk, first, second, ep}:
      Position{Game.White{}, wk, dest, first, second, NoEP{}}

def after_pawn(second: Bool, position: Position, file: Word(3n), rights: Rights) -> Position:
  match second position:
    case False{} Position{turn, wk, bk, Seed{owner, old}, second, ep}:
      Position{Three.other(turn), wk, bk, Seed{owner, file}, second, rights}
    case True{} Position{turn, wk, bk, first, Seed{owner, old}, ep}:
      Position{Three.other(turn), wk, bk, first, Seed{owner, file}, rights}

def king_edge(takes_first: Bool, takes_second: Bool, +a: Nat, +b: Nat, position: Position) -> Edge:
  match takes_first takes_second:
    case True{} _:
      KPK{Pawn.board(b, pawn_position(True{}, position))}
    case False{} True{}:
      KPK{Pawn.board(a, pawn_position(False{}, position))}
    case False{} False{}:
      Quiet{position}

def push_edge(takes: Bool, second: Bool, next: Nat, position: Position) -> Edge:
  match takes second:
    case True{} _:
      KPK{Pawn.board(next, pawn_position(second, position))}
    case False{} False{}:
      FirstPush{position}
    case False{} True{}:
      SecondPush{position}

def promoted(takes: Bool, +second: Bool, remaining: Nat, +position: Position, kind: Three.Material) -> Edge:
  match takes:
    case True{}:
      Pawnless{Material.from_three(kind, Pawn.board(0n, pawn_position(second, position)))}
    case False{}:
      Promoted{remaining, One.Position{pawn_position(Bool.not(second), position),
        Material.Man{owner(seed(second, position)), kind, square(0n, seed(second, position))}}}

def after(+a: Nat, +b: Nat, +position: Position, action: Action) -> Edge:
  match a b action:
    case _ _ King{+dest}:
      king_edge(Material.equal(dest, square(a, seed(False{}, position))), Material.equal(dest, square(b, seed(True{}, position))),
        a, b, after_king(position, dest))
    case 1n+prior _ Step{False{}, +file}:
      push_edge(Material.equal(Pawn.square(Pawn.rank(prior, owner(seed(False{}, position))), file), square(b, seed(True{}, position))),
        False{}, prior, after_pawn(False{}, position, file, NoEP{}))
    case _ 1n+prior Step{True{}, +file}:
      push_edge(Material.equal(Pawn.square(Pawn.rank(prior, owner(seed(True{}, position))), file), square(a, seed(False{}, position))),
        True{}, prior, after_pawn(True{}, position, file, NoEP{}))
    case _ _ Double{False{}}:
      FirstDouble{after_pawn(False{}, position, file_of(seed(False{}, position)), FirstEP{})}
    case _ _ Double{True{}}:
      SecondDouble{after_pawn(True{}, position, file_of(seed(True{}, position)), SecondEP{})}
    case _ _ Promote{False{}, +file, kind}:
      promoted(Material.equal(Pawn.square(Pawn.rank(0n, owner(seed(False{}, position))), file), square(b, seed(True{}, position))),
        False{}, b, after_pawn(False{}, position, file, NoEP{}), kind)
    case _ _ Promote{True{}, +file, kind}:
      promoted(Material.equal(Pawn.square(Pawn.rank(0n, owner(seed(True{}, position))), file), square(a, seed(False{}, position))),
        True{}, a, after_pawn(True{}, position, file, NoEP{}), kind)
    case _ _ EnPassant{+second}:
      KPK{Pawn.board(2n, pawn_position(second,
        after_pawn(second, position, file_of(seed(Bool.not(second), position)), NoEP{})))}
    case _ _ _:
      Quiet{position}

def double_first(prior: Nat, b: Nat, position: Position) -> Bool:
  match prior:
    case 0n:
      False{}
    case 1n+rest:
      valid(rest, b, position)

def double_second(a: Nat, prior: Nat, position: Position) -> Bool:
  match prior:
    case 0n:
      False{}
    case 1n+rest:
      valid(a, rest, position)

def safe(+a: Nat, +b: Nat, edge: Edge) -> Bool:
  match a b edge:
    case _ _ Quiet{position}:
      valid(a, b, position)
    case 1n+prior _ FirstPush{position}:
      valid(prior, b, position)
    case _ 1n+prior SecondPush{position}:
      valid(a, prior, position)
    case 1n+prior _ FirstDouble{position}:
      double_first(prior, b, position)
    case _ 1n+prior SecondDouble{position}:
      double_second(a, prior, position)
    case _ _ KPK{board}:
      Pawn.valid_board(board)
    case _ _ Promoted{advance, position}:
      One.valid(advance, position)
    case _ _ Pawnless{position}:
      Material.valid(position)
    case _ _ _:
      False{}

def landing(+a: Nat, +b: Nat, +second: Bool, next: Nat, +position: Position, +file: Word(3n)) -> Bool:
  +moving = seed(second, position)
  +other = seed(Bool.not(second), position)
  +dest = Pawn.square(Pawn.rank(next, owner(moving)), file)
  Three.same(owner(moving), turn(position)) &&
    ((U32.is_eq(Three.number(3n, file_of(moving)), Three.number(3n, file)) && empty(a, b, position, dest)) ||
     (U32.is_eq(Geometry.distance(Three.number(3n, file_of(moving)), Three.number(3n, file)), 1) &&
       Bool.not(Three.same(owner(moving), owner(other))) &&
       Material.equal(dest, square(Bool.pick(Nat, second, a, b), other))))

def ep_allowed(+a: Nat, +b: Nat, +second: Bool, +position: Position) -> Bool:
  match a b second position:
    case 3n 4n False{} Position{+turn, wk, bk, +first, +other, SecondEP{}}:
      Three.same(owner(first), turn) && Bool.not(Three.same(owner(first), owner(other))) &&
        U32.is_eq(Geometry.distance(Three.number(3n, file_of(first)), Three.number(3n, file_of(other))), 1) &&
        empty(3n, 4n, position, Pawn.square(Pawn.rank(2n, owner(first)), file_of(other)))
    case 4n 3n True{} Position{+turn, wk, bk, +other, +second, FirstEP{}}:
      Three.same(owner(second), turn) && Bool.not(Three.same(owner(second), owner(other))) &&
        U32.is_eq(Geometry.distance(Three.number(3n, file_of(second)), Three.number(3n, file_of(other))), 1) &&
        empty(4n, 3n, position, Pawn.square(Pawn.rank(2n, owner(second)), file_of(other)))
    case _ _ _ _:
      False{}

def pseudo(+a: Nat, +b: Nat, +position: Position, action: Action) -> Bool:
  match a b action:
    case _ _ King{+dest}:
      Geometry.king_step(Three.number(6n, king(turn(position), position)), Three.number(6n, dest)) &&
        Bool.not(Three.same(owner(seed(False{}, position)), turn(position)) && Material.equal(dest, square(a, seed(False{}, position)))) &&
        Bool.not(Three.same(owner(seed(True{}, position)), turn(position)) && Material.equal(dest, square(b, seed(True{}, position))))
    case 1n+1n+rest _ Step{False{}, file}:
      landing(a, b, False{}, 1n+rest, position, file)
    case _ 1n+1n+rest Step{True{}, file}:
      landing(a, b, True{}, 1n+rest, position, file)
    case 6n _ Double{False{}}:
      Three.same(owner(seed(False{}, position)), turn(position)) &&
        empty(a, b, position, square(5n, seed(False{}, position))) && empty(a, b, position, square(4n, seed(False{}, position)))
    case _ 6n Double{True{}}:
      Three.same(owner(seed(True{}, position)), turn(position)) &&
        empty(a, b, position, square(5n, seed(True{}, position))) && empty(a, b, position, square(4n, seed(True{}, position)))
    case 1n _ Promote{False{}, file, kind}:
      landing(a, b, False{}, 0n, position, file)
    case _ 1n Promote{True{}, file, kind}:
      landing(a, b, True{}, 0n, position, file)
    case _ _ EnPassant{second}:
      ep_allowed(a, b, second, position)
    case _ _ _:
      False{}

def legal(+a: Nat, +b: Nat, +position: Position, +action: Action) -> Bool:
  (valid(a, b, position) && pseudo(a, b, position, action)) && safe(a, b, after(a, b, position, action))

# Compact action codes; all meaningful actions have a canonical encoding.
def action(key: Word(8n)) -> Action:
  match key:
    case WCon{False{}, WCon{ignored, dest}}:
      King{dest}
    case WCon{True{}, WCon{second, WCon{False{}, WCon{False{}, WCon{False{}, file}}}}}:
      Step{second, file}
    case WCon{True{}, WCon{second, WCon{False{}, WCon{False{}, WCon{True{}, file}}}}}:
      Double{second}
    case WCon{True{}, WCon{second, WCon{False{}, WCon{True{}, WCon{False{}, file}}}}}:
      Promote{second, file, Three.Queen{}}
    case WCon{True{}, WCon{second, WCon{False{}, WCon{True{}, WCon{True{}, file}}}}}:
      Promote{second, file, Three.Rook{}}
    case WCon{True{}, WCon{second, WCon{True{}, WCon{False{}, WCon{False{}, file}}}}}:
      Promote{second, file, Three.Bishop{}}
    case WCon{True{}, WCon{second, WCon{True{}, WCon{False{}, WCon{True{}, file}}}}}:
      Promote{second, file, Three.Knight{}}
    case WCon{True{}, WCon{second, WCon{True{}, WCon{True{}, WCon{False{}, file}}}}}:
      EnPassant{second}
    case _:
      Unused{}

def encode(move: Action) -> Word(8n):
  match move:
    case King{dest}:
      WCon{False{}, WCon{False{}, dest}}
    case Step{second, file}:
      WCon{True{}, WCon{second, WCon{False{}, WCon{False{}, WCon{False{}, file}}}}}
    case Double{second}:
      WCon{True{}, WCon{second, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}
    case Promote{second, file, Three.Queen{}}:
      WCon{True{}, WCon{second, WCon{False{}, WCon{True{}, WCon{False{}, file}}}}}
    case Promote{second, file, Three.Rook{}}:
      WCon{True{}, WCon{second, WCon{False{}, WCon{True{}, WCon{True{}, file}}}}}
    case Promote{second, file, Three.Bishop{}}:
      WCon{True{}, WCon{second, WCon{True{}, WCon{False{}, WCon{False{}, file}}}}}
    case Promote{second, file, Three.Knight{}}:
      WCon{True{}, WCon{second, WCon{True{}, WCon{False{}, WCon{True{}, file}}}}}
    case EnPassant{second}:
      WCon{True{}, WCon{second, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}
    case Unused{}:
      WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}

def action_at(+width: Nat, key: Word(width)) -> Action:
  action(Index.fit(8n, width, key))

def encode_at(width: Nat, move: Action) -> Word(width):
  Index.fit(width, 8n, encode(move))

def include(allowed: Bool, next: Edge, tail: List<&2, Edge>) -> List<&2, Edge>:
  match allowed:
    case True{}:
      next <> tail
    case False{}:
      tail

def successors.go(depth: Nat, +width: Nat, +a: Nat, +b: Nat, +position: Position,
  keys: Finite.Table(depth, Word(width)), tail: List<&2, Edge>) -> List<&2, Edge>:
  match depth keys:
    case 0n +key:
      include(legal(a, b, position, action_at(width, key)), after(a, b, position, action_at(width, key)), tail)
    case 1n++rest Finite.Fork{left, right}:
      successors.go(rest, width, a, b, position, left, successors.go(rest, width, a, b, position, right, tail))

def successors(+width: Nat, a: Nat, b: Nat, position: Position) -> List<&2, Edge>:
  successors.go(width, width, a, b, position, Finite.keys(width), Nil{})

def Member(+next: Edge, states: List<&2, Edge>) -> Type:
  match states:
    case Nil{}:
      Empty
    case head <> tail:
      {next == head : Edge} | Member(next, tail)

def LegalSuccessor(+width: Nat, +a: Nat, +b: Nat, +position: Position, +next: Edge) -> Type:
  &key: Word(width) -> Game.Truth(legal(a, b, position, action_at(width, key))) &
    {next == after(a, b, position, action_at(width, key)) : Edge}
