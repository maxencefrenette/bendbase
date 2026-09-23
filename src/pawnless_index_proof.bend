import Base
import ./pawnless_index.bend as Index
import ./pawnless_chess.bend as Chess
import ./game.bend as Game
import ./word_parts.bend as Parts

def split_append(n: Nat, +m: Nat, +low: Word(n), +high: Word(m)) ->
  {Parts.split(m, n, Parts.append(m, n, low, high)) == (low, high) : Word(n) & Word(m)}:
  match n low:
    case 0n WNil{}:
      {==}
    case 1n++rest WCon{+bit, +tail}:
      Equal.cong(Word(rest) & Word(m), Word(1n+rest) & Word(m),
        pair => Parts.split.prepend(rest, m, bit, pair),
        Parts.split(m, rest, Parts.append(m, rest, tail, high)),
        (tail, high), split_append(rest, m, tail, high))

def player_bit(+player: Game.Player) -> {Index.player(Index.bit(player)) == player : Game.Player}:
  match player:
    case Game.White{}:
      {==}
    case Game.Black{}:
      {==}

def decode_encode(+board: Chess.Board) -> {Index.decode(Index.encode(board)) == board : Chess.Board}:
  match board:
    case Chess.Board{+owner, +turn, +wk, +bk, +pc}:
      %player_bit(owner) :
        {Index.decode(Index.encode(board)) == Chess.Board{_, turn, wk, bk, pc} : Chess.Board}
      %player_bit(turn) :
        {Index.decode(Index.encode(board)) == Chess.Board{Index.player(Index.bit(owner)), _, wk, bk, pc} : Chess.Board}
      Equal.trans(Chess.Board,
        Index.decode(Index.encode(board)),
        Index.decode.pieces(Index.player(Index.bit(owner)), Index.player(Index.bit(turn)),
          (pc, Parts.append(6n, 6n, bk, wk))),
        Chess.Board{Index.player(Index.bit(owner)), Index.player(Index.bit(turn)), wk, bk, pc},
        Equal.cong(Word(6n) & Word(12n), Chess.Board,
          pair => Index.decode.pieces(Index.player(Index.bit(owner)), Index.player(Index.bit(turn)), pair),
          Parts.split(12n, 6n, Parts.append(12n, 6n, pc, Parts.append(6n, 6n, bk, wk))),
          (pc, Parts.append(6n, 6n, bk, wk)), split_append(6n, 12n, pc, Parts.append(6n, 6n, bk, wk))),
        Equal.cong(Word(6n) & Word(6n), Chess.Board,
          pair => Index.decode.kings(Index.player(Index.bit(owner)), Index.player(Index.bit(turn)), pc, pair),
          Parts.split(6n, 6n, Parts.append(6n, 6n, bk, wk)), (bk, wk), split_append(6n, 6n, bk, wk)))

def fit_identity(n: Nat, +word: Word(n)) -> {Index.fit(n, n, word) == word : Word(n)}:
  match n word:
    case 0n WNil{}:
      {==}
    case 1n++rest WCon{+bit, +tail}:
      %fit_identity(rest, tail) : {WCon{bit, Index.fit(rest, rest, tail)} == WCon{bit, _} : Word(1n+rest)}
      {==}

def roundtrip_at(+width: Nat, size: {width == 20n : Nat}, +board: Chess.Board) ->
  {Index.decode_at(width, Index.encode_at(width, board)) == board : Chess.Board}:
  Equal.trans(Chess.Board, Index.decode_at(width, Index.encode_at(width, board)),
    Index.decode_at(20n, Index.encode_at(20n, board)), board,
    Equal.cong(Nat, Chess.Board, n => Index.decode_at(n, Index.encode_at(n, board)), width, 20n, size),
    Equal.trans(Chess.Board, Index.decode_at(20n, Index.encode_at(20n, board)),
      Index.decode(Index.encode(board)), board,
      Equal.cong(Word(20n), Chess.Board, word => Index.decode(word),
        Index.fit(20n, 20n, Index.fit(20n, 20n, Index.encode(board))), Index.encode(board),
        Equal.trans(Word(20n), Index.fit(20n, 20n, Index.fit(20n, 20n, Index.encode(board))),
          Index.fit(20n, 20n, Index.encode(board)), Index.encode(board),
          fit_identity(20n, Index.fit(20n, 20n, Index.encode(board))), fit_identity(20n, Index.encode(board)))),
      decode_encode(board)))
