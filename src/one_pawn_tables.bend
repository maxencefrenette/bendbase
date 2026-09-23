import Base
import ./game.bend as Game
import ./pawnless_chess.bend as Three
import ./pawn_chess.bend as Pawn
import ./material_chess.bend as Material
import ./four_index.bend as Index
import ./one_pawn_chess.bend as Chess
import ./one_pawn_solver.bend as Solver
import ./finite_table.bend as Finite
import ./pawnless_tables.bend as Bytes

# In the shared 26-bit layout, the first piece is the pawn and the second
# is the Q/R/B/N. Both pawn colors and both turns are represented in each file.
type Profile is Data:
  Profile{kind: Three.Material, opposed: Bool}

def advance(board: Index.Board) -> Nat:
  match board:
    case Index.Board{base, second}:
      Pawn.advance(base)

def position(profile: Profile, board: Index.Board) -> Chess.Position:
  match profile board:
    case Profile{kind, opposed} Index.Board{Three.Board{+owner, turn, wk, bk, WCon{a, WCon{b, WCon{c, file}}}}, at}:
      Chess.Position{Pawn.Position{owner, turn, wk, bk, file},
        Material.Man{Bool.pick(Game.Player, opposed, Three.other(owner), owner), kind, at}}

def value(limit: Nat, moves: Nat, other_moves: Nat, profile: Profile, +board: Index.Board) -> Game.Outcome:
  Solver.value(limit, moves, other_moves, advance(board), position(profile, board))

def entries(depth: Nat, +width: Nat, +limit: Nat, +moves: Nat, +other_moves: Nat, +profile: Profile,
  keys: Finite.Table(depth, Word(width))) -> Finite.Table(depth, Game.Outcome):
  match depth keys:
    case 0n key:
      value(limit, moves, other_moves, profile, Index.decode_at(width, key))
    case 1n++rest Finite.Fork{left, right}:
      a b = entries(rest, width, limit, moves, other_moves, profile, left) entries(rest, width, limit, moves, other_moves, profile, right)
      Finite.Fork{a, b}

def generate(+width: Nat, limit: Nat, moves: Nat, other_moves: Nat, profile: Profile) -> Finite.Table(width, Game.Outcome):
  entries(width, width, limit, moves, other_moves, profile, Finite.keys(width))

def file(+width: Nat, limit: Nat, moves: Nat, other_moves: Nat, profile: Profile) -> List<&2, U32>:
  Finite.flatten(width, Bytes.bytes(width, generate(width, limit, moves, other_moves, profile)))
