import Base
import ./game.bend as Game
import ./pawnless_chess.bend as Three
import ./pawn_chess.bend as Pawn
import ./material_chess.bend as Material
import ./geometry.bend as Geometry
import ./finite_table.bend as Finite
import ./pawnless_index.bend as Index

# Exactly two kings, one pawn and one Q/R/B/N. Pawn distance is its actual
# rank relative to promotion. There is no en passant with only one pawn.
type Position is Data:
  Position{pawn: Pawn.Position, extra: Material.Man}

type Action is Data:
  King{dest: Word(6n)}
  Piece{dest: Word(6n)}
  Step{file: Word(3n)}
  Double{}
  Promote{file: Word(3n), kind: Three.Material}
  Unused{}

type Edge is Data:
  Quiet{position: Position}
  Push{position: Position}
  DoublePush{position: Position}
  KPK{board: Three.Board}
  Pawnless{position: Material.Position}

def pawn(position: Position) -> Pawn.Position:
  match position:
    case Position{pawn, extra}:
      pawn

def extra(position: Position) -> Material.Man:
  match position:
    case Position{pawn, extra}:
      extra

def turn(position: Position) -> Game.Player:
  Pawn.turn(pawn(position))

def pawn_square(advance: Nat, position: Position) -> Word(6n):
  match position:
    case Position{Pawn.Position{owner, turn, wk, bk, file}, extra}:
      Pawn.square(Pawn.rank(advance, owner), file)

def bare(position: Position) -> Material.Position:
  match position:
    case Position{Pawn.Position{owner, turn, wk, bk, file}, extra}:
      Material.Position{turn, wk, bk, extra <> Nil{}}

# The synthetic kind below is used ONLY as an occupancy blocker in attacks;
# pawn attacks are computed separately. Never call Material.checked on it.
def occupancy(+advance: Nat, +position: Position) -> Material.Position:
  match position:
    case Position{Pawn.Position{owner, turn, wk, bk, file}, extra}:
      Material.Position{turn, wk, bk, Material.Man{owner, Three.Queen{}, pawn_square(advance, position)} <> extra <> Nil{}}

def checked(+advance: Nat, +position: Position, +player: Game.Player) -> Bool:
  match position:
    case Position{Pawn.Position{+owner, turn, wk, bk, file}, Material.Man{other, kind, at}}:
      +target = Material.king(bare(position), player)
      Geometry.kings_touch(Three.number(6n, wk), Three.number(6n, bk)) ||
        (Bool.not(Three.same(owner, player)) && Pawn.attacks(advance, pawn(position), target)) ||
        (Bool.not(Three.same(other, player)) && Material.attacks(kind, at, target, occupancy(advance, position)))

def valid(+advance: Nat, +position: Position) -> Bool:
  match position:
    case Position{Pawn.Position{owner, +turn, +wk, +bk, file}, +extra}:
      Pawn.on_board(advance) && Bool.not(Material.equal(wk, bk)) &&
        Material.distinct(Material.Man{owner, Three.Queen{}, pawn_square(advance, position)} <> extra <> Nil{}, wk, bk) &&
        Bool.not(Geometry.kings_touch(Three.number(6n, wk), Three.number(6n, bk))) &&
        Bool.not(checked(advance, position, Three.other(turn)))

def extra_square(position: Position) -> Word(6n):
  match position:
    case Position{pawn, Material.Man{owner, kind, at}}:
      at

def friendly(+advance: Nat, +position: Position, +dest: Word(6n)) -> Bool:
  match position:
    case Position{Pawn.Position{owner, +turn, wk, bk, file}, Material.Man{other, kind, at}}:
      (Three.same(owner, turn) && Material.equal(pawn_square(advance, position), dest)) ||
        (Three.same(other, turn) && Material.equal(at, dest))

def empty(+position: Position, +dest: Word(6n)) -> Bool:
  match position:
    case Position{Pawn.Position{owner, turn, wk, bk, file}, Material.Man{other, kind, at}}:
      Bool.not(Material.equal(dest, wk)) && Bool.not(Material.equal(dest, bk)) && Bool.not(Material.equal(dest, at))

def push_pawn(pawn: Pawn.Position, file: Word(3n)) -> Pawn.Position:
  match pawn:
    case Pawn.Position{owner, turn, wk, bk, old}:
      Pawn.Position{owner, Three.other(turn), wk, bk, file}

def after_king(position: Position, dest: Word(6n)) -> Position:
  match position:
    case Position{pawn, extra}:
      Position{Pawn.after_king(pawn, dest), extra}

def after_piece(position: Position, dest: Word(6n)) -> Position:
  match position:
    case Position{pawn, Material.Man{owner, kind, at}}:
      Position{Pawn.after_push(pawn), Material.Man{owner, kind, dest}}

def king_edge(takes_pawn: Bool, takes_piece: Bool, +advance: Nat, position: Position) -> Edge:
  match takes_pawn takes_piece:
    case True{} _:
      Pawnless{bare(position)}
    case False{} True{}:
      KPK{Pawn.board(advance, pawn(position))}
    case False{} False{}:
      Quiet{position}

def piece_edge(takes_pawn: Bool, position: Position) -> Edge:
  match takes_pawn:
    case True{}:
      Pawnless{bare(position)}
    case False{}:
      Quiet{position}

def push_edge(takes_piece: Bool, advance: Nat, pawn: Pawn.Position, extra: Material.Man) -> Edge:
  match takes_piece:
    case True{}:
      KPK{Pawn.board(advance, pawn)}
    case False{}:
      Push{Position{pawn, extra}}

def promote_position(takes_piece: Bool, pawn: Pawn.Position, extra: Material.Man, kind: Three.Material) -> Material.Position:
  match takes_piece pawn:
    case True{} Pawn.Position{+owner, turn, wk, bk, file}:
      Material.Position{turn, wk, bk, Material.Man{owner, kind, Pawn.square(Pawn.rank(0n, owner), file)} <> Nil{}}
    case False{} Pawn.Position{+owner, turn, wk, bk, file}:
      Material.Position{turn, wk, bk, Material.Man{owner, kind, Pawn.square(Pawn.rank(0n, owner), file)} <> extra <> Nil{}}

def destination(advance: Nat, position: Position, file: Word(3n)) -> Word(6n):
  match position:
    case Position{Pawn.Position{owner, turn, wk, bk, old}, extra}:
      Pawn.square(Pawn.rank(advance, owner), file)

def after(+advance: Nat, +position: Position, action: Action) -> Edge:
  match advance action:
    case _ King{+dest}:
      king_edge(Material.equal(dest, pawn_square(advance, position)), Material.equal(dest, extra_square(position)),
        advance, after_king(position, dest))
    case _ Piece{+dest}:
      piece_edge(Material.equal(dest, pawn_square(advance, position)), after_piece(position, dest))
    case 1n+prior Step{+file}:
      push_edge(Material.equal(destination(prior, position, file), extra_square(position)), prior,
        push_pawn(pawn(position), file), extra(position))
    case _ Double{}:
      DoublePush{Position{Pawn.after_push(pawn(position)), extra(position)}}
    case _ Promote{+file, kind}:
      Pawnless{promote_position(Material.equal(destination(0n, position, file), extra_square(position)),
        push_pawn(pawn(position), file), extra(position), kind)}
    case _ _:
      Quiet{position}

def double_safe(prior: Nat, position: Position) -> Bool:
  match prior:
    case 0n:
      False{}
    case 1n+rest:
      valid(rest, position)

def safe(advance: Nat, edge: Edge) -> Bool:
  match advance edge:
    case _ Quiet{position}:
      valid(advance, position)
    case 1n+prior Push{position}:
      valid(prior, position)
    case 1n+prior DoublePush{position}:
      double_safe(prior, position)
    case _ KPK{board}:
      Pawn.valid_board(board)
    case _ Pawnless{position}:
      Material.valid(position)
    case _ _:
      False{}

# A pawn advances straight into an empty square or diagonally onto the lone
# enemy non-king piece. Both cases share the post-move king-safety check.
def pawn_landing(+next: Nat, +position: Position, +file: Word(3n)) -> Bool:
  match position:
    case Position{Pawn.Position{owner, +turn, wk, bk, +old}, Material.Man{other, kind, +at}}:
      +dest = destination(next, position, file)
      Three.same(owner, turn) &&
        ((U32.is_eq(Three.number(3n, old), Three.number(3n, file)) && empty(position, dest)) ||
         (U32.is_eq(Geometry.distance(Three.number(3n, old), Three.number(3n, file)), 1) &&
          Bool.not(Three.same(other, turn)) && Material.equal(at, dest)))

def piece_geometry(+advance: Nat, +position: Position, +dest: Word(6n)) -> Bool:
  match position:
    case Position{Pawn.Position{owner, +turn, wk, bk, file}, Material.Man{other, kind, at}}:
      Three.same(other, turn) && Material.attacks(kind, at, dest, occupancy(advance, position)) &&
        Bool.not(Material.equal(dest, wk)) && Bool.not(Material.equal(dest, bk)) &&
        Bool.not(friendly(advance, position, dest))

def pseudo(+advance: Nat, +position: Position, action: Action) -> Bool:
  match advance action:
    case _ King{+dest}:
      Geometry.king_step(Three.number(6n, Material.king(bare(position), turn(position))), Three.number(6n, dest)) &&
        Bool.not(friendly(advance, position, dest))
    case _ Piece{dest}:
      piece_geometry(advance, position, dest)
    case 1n+1n+rest Step{file}:
      pawn_landing(1n+rest, position, file)
    case 6n Double{}:
      Pawn.owns_turn(pawn(position)) && empty(position, pawn_square(5n, position)) && empty(position, pawn_square(4n, position))
    case 1n Promote{file, kind}:
      pawn_landing(0n, position, file)
    case _ _:
      False{}

def legal(+advance: Nat, +position: Position, +action: Action) -> Bool:
  (valid(advance, position) && pseudo(advance, position, action)) && safe(advance, after(advance, position, action))

# Eight-bit action domain: king and piece destinations, then pawn file and
# promotion choice. Reserved encodings are illegal.
def action(key: Word(8n)) -> Action:
  match key:
    case WCon{False{}, WCon{False{}, dest}}:
      King{dest}
    case WCon{False{}, WCon{True{}, dest}}:
      Piece{dest}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, file}}}}}:
      Step{file}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, file}}}}}:
      Double{}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, file}}}}}:
      Promote{file, Three.Queen{}}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, file}}}}}:
      Promote{file, Three.Rook{}}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, file}}}}}:
      Promote{file, Three.Bishop{}}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, file}}}}}:
      Promote{file, Three.Knight{}}
    case _:
      Unused{}

def encode(move: Action) -> Word(8n):
  match move:
    case King{dest}:
      WCon{False{}, WCon{False{}, dest}}
    case Piece{dest}:
      WCon{False{}, WCon{True{}, dest}}
    case Step{file}:
      WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, file}}}}}
    case Double{}:
      WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}
    case Promote{file, Three.Queen{}}:
      WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, file}}}}}
    case Promote{file, Three.Rook{}}:
      WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, file}}}}}
    case Promote{file, Three.Bishop{}}:
      WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, file}}}}}
    case Promote{file, Three.Knight{}}:
      WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, file}}}}}
    case Unused{}:
      WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}

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

def successors.go(depth: Nat, +width: Nat, +advance: Nat, +position: Position,
  keys: Finite.Table(depth, Word(width)), tail: List<&2, Edge>) -> List<&2, Edge>:
  match depth keys:
    case 0n +key:
      include(legal(advance, position, action_at(width, key)), after(advance, position, action_at(width, key)), tail)
    case 1n++rest Finite.Fork{left, right}:
      successors.go(rest, width, advance, position, left, successors.go(rest, width, advance, position, right, tail))

def successors(+width: Nat, advance: Nat, position: Position) -> List<&2, Edge>:
  successors.go(width, width, advance, position, Finite.keys(width), Nil{})

def Member(+next: Edge, states: List<&2, Edge>) -> Type:
  match states:
    case Nil{}:
      Empty
    case head <> tail:
      {next == head : Edge} | Member(next, tail)

def LegalSuccessor(+width: Nat, +advance: Nat, +position: Position, +next: Edge) -> Type:
  &key: Word(width) -> Game.Truth(legal(advance, position, action_at(width, key))) &
    {next == after(advance, position, action_at(width, key)) : Edge}
