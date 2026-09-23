import Base
import ./four_index.bend as Index
import ./pawnless_index.bend as Three
import ./pawnless_index_proof.bend as Proof
import ./word_parts.bend as Parts
import ./pawnless_chess.bend as Chess

def roundtrip(+board: Index.Board) -> {Index.decode(Index.encode(board)) == board : Index.Board}:
  match board:
    case Index.Board{+base, +second}:
      Equal.trans(Index.Board, Index.decode(Index.encode(board)),
        Index.Board{Three.decode(Three.encode(base)), second}, board,
        Equal.cong(Word(6n) & Word(20n), Index.Board, pair => Index.decode.parts(pair),
          Parts.split(20n, 6n, Parts.append(20n, 6n, second, Three.encode(base))), (second, Three.encode(base)),
          Proof.split_append(6n, 20n, second, Three.encode(base))),
        Equal.cong(Chess.Board, Index.Board, b => Index.Board{b, second},
          Three.decode(Three.encode(base)), base, Proof.decode_encode(base)))

def roundtrip_at(+width: Nat, size: {width == 26n : Nat}, +board: Index.Board) ->
  {Index.decode_at(width, Index.encode_at(width, board)) == board : Index.Board}:
  Equal.trans(Index.Board, Index.decode_at(width, Index.encode_at(width, board)),
    Index.decode_at(26n, Index.encode_at(26n, board)), board,
    Equal.cong(Nat, Index.Board, n => Index.decode_at(n, Index.encode_at(n, board)), width, 26n, size),
    Equal.trans(Index.Board, Index.decode_at(26n, Index.encode_at(26n, board)), Index.decode(Index.encode(board)), board,
      Equal.cong(Word(26n), Index.Board, key => Index.decode(key),
        Three.fit(26n, 26n, Three.fit(26n, 26n, Index.encode(board))), Index.encode(board),
        Equal.trans(Word(26n), Three.fit(26n, 26n, Three.fit(26n, 26n, Index.encode(board))),
          Three.fit(26n, 26n, Index.encode(board)), Index.encode(board),
          Proof.fit_identity(26n, Three.fit(26n, 26n, Index.encode(board))), Proof.fit_identity(26n, Index.encode(board)))), roundtrip(board)))
