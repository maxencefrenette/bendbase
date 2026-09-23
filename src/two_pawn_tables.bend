import Base
import ./game.bend as Game
import ./pawnless_chess.bend as Three
import ./pawn_chess.bend as Pawn
import ./four_index.bend as Index
import ./two_pawn_chess.bend as Chess
import ./two_pawn_game.bend as Rules
import ./finite_table.bend as Finite
import ./pawnless_tables.bend as Bytes

# Reuse the 26-bit board layout: first pawn in base.pc, second in second.
# Store only NoEP roots at clock zero. Double pushes create transient EP rights
# in Rules.tree; ignoring those continuations would give incorrect WDL.
# False = KPPK (same owner); True = KPKP (opposite owners).
type Profile is Data:
  Profile{opposed: Bool}

def first_advance(board: Index.Board) -> Nat:
  match board:
    case Index.Board{base, second}:
      Pawn.advance(base)

def second_owner(profile: Profile, +owner: Game.Player) -> Game.Player:
  match profile:
    case Profile{opposed}:
      Bool.pick(Game.Player, opposed, Three.other(owner), owner)

def second_advance(profile: Profile, board: Index.Board) -> Nat:
  match board:
    case Index.Board{Three.Board{owner, turn, wk, bk, pc}, WCon{a, WCon{b, WCon{c, file}}}}:
      Pawn.distance(second_owner(profile, owner), WCon{a, WCon{b, WCon{c, WNil{}}}})

def position(+profile: Profile, board: Index.Board) -> Chess.Position:
  match board:
    case Index.Board{Three.Board{+owner, turn, wk, bk, WCon{a, WCon{b, WCon{c, file}}}},
      WCon{d, WCon{e, WCon{f, other_file}}}}:
      Chess.Position{turn, wk, bk, Chess.Seed{owner, file},
        Chess.Seed{second_owner(profile, owner), other_file}, Chess.NoEP{}}

# Use the already-proved generic minimax directly: no duplicate solver or
# solver-equivalence induction. This is a slow, pure reference definition.
def value(limit: Nat, moves: Nat, other_moves: Nat, +profile: Profile, +board: Index.Board) -> Game.Outcome:
  Game.evaluate(Rules.tree(limit, moves, other_moves, first_advance(board), second_advance(profile, board), position(profile, board)))

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
