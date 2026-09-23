import Base
import ./pawnless_chess.bend as Chess
import ./game.bend as Game
import ./word_parts.bend as WordParts

def bit(player: Game.Player) -> Bool:
  match player:
    case Game.White{}:
      False{}
    case Game.Black{}:
      True{}

def player(bit: Bool) -> Game.Player:
  match bit:
    case False{}:
      Game.White{}
    case True{}:
      Game.Black{}

# MSB first: owner, turn, piece[5..0], black king[5..0], white king[5..0].
def encode(board: Chess.Board) -> Word(20n):
  match board:
    case Chess.Board{owner, turn, wk, bk, pc}:
      WCon{bit(owner), WCon{bit(turn),
        WordParts.append(12n, 6n, pc, WordParts.append(6n, 6n, bk, wk))}}

def decode.kings(owner: Game.Player, turn: Game.Player, pc: Word(6n),
  pair: Word(6n) & Word(6n)) -> Chess.Board:
  match pair:
    case Tuple{bk, wk}:
      Chess.Board{owner, turn, wk, bk, pc}

def decode.pieces(owner: Game.Player, turn: Game.Player,
  pair: Word(6n) & Word(12n)) -> Chess.Board:
  match pair:
    case Tuple{pc, kings}:
      decode.kings(owner, turn, pc, WordParts.split(6n, 6n, kings))

def decode(key: Word(20n)) -> Chess.Board:
  match key:
    case WCon{owner, WCon{turn, pieces}}:
      decode.pieces(player(owner), player(turn), WordParts.split(12n, 6n, pieces))

# Width is kept symbolic in the table induction; the public correctness law
# requires width=20. At that width fit is the identity (proved structurally).
def fit(n: Nat, m: Nat, word: Word(m)) -> Word(n):
  match n m word:
    case 0n _ _:
      WNil{}
    case 1n+rest 0n WNil{}:
      WCon{False{}, fit(rest, 0n, WNil{})}
    case 1n+rest 1n+more WCon{bit, tail}:
      WCon{bit, fit(rest, more, tail)}

def encode_at(width: Nat, board: Chess.Board) -> Word(width):
  fit(width, 20n, encode(board))

def decode_at(+width: Nat, key: Word(width)) -> Chess.Board:
  decode(fit(20n, width, key))
