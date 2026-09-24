import Base
import ./chess.bend as C
import ./position.bend as P
import ./game.bend as G
import ./pawnless_chess.bend as Three
import ./word_parts.bend as W
import ./chess_measure.bend as M
import ./chess_measure_proof.bend as Proof
import ./geometry.bend as Geometry

def and_intro(+a: Bool, +b: Bool, left: G.Truth(a), right: G.Truth(b)) -> G.Truth(a && b):
  match a:
    case True{}:
      right
    case False{}:
      match left:

def word_refl(n: Nat, +a: Word(n)) -> {W.equal(n, a, a) == True{} : Bool}:
  match n a:
    case 0n WNil{}:
      {==}
    case 1n+rest WCon{False{}, tail}:
      word_refl(rest, tail)
    case 1n+rest WCon{True{}, tail}:
      word_refl(rest, tail)

def word_reflect(+n: Nat, +a: Word(n), +b: Word(n), yes: G.Truth(W.equal(n, a, b))) -> {a == b : Word(n)}:
  match n a b:
    case 0n WNil{} WNil{}:
      {==}
    case 1n+rest WCon{False{}, x} WCon{False{}, y}:
      %word_reflect(rest, x, y, yes) : {WCon{False{}, x} == WCon{False{}, _} : Word(1n+rest)}
      {==}
    case 1n+rest WCon{True{}, x} WCon{True{}, y}:
      %word_reflect(rest, x, y, yes) : {WCon{True{}, x} == WCon{True{}, _} : Word(1n+rest)}
      {==}
    case 1n+rest WCon{False{}, x} WCon{True{}, y}:
      match yes:
    case 1n+rest WCon{True{}, x} WCon{False{}, y}:
      match yes:

def yes_equal(+b: Bool, yes: G.Truth(b)) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      match yes:

def no_equal(+b: Bool, no: G.Truth(Bool.not(b))) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      match no:

def split(-A: Type, +b: Bool, yes: G.Truth(b) -> A, no: G.Truth(Bool.not(b)) -> A) -> A:
  match b:
    case True{}:
      yes(Unit{})
    case False{}:
      no(Unit{})

def contradiction(-A: Type, +b: Bool, yes: G.Truth(b), no: G.Truth(Bool.not(b))) -> A:
  match b:
    case True{}:
      match no:
    case False{}:
      match yes:

def no_left(+a: Bool, +b: Bool, no: G.Truth(Bool.not(a || b))) -> G.Truth(Bool.not(a)):
  match a b:
    case False{} False{}:
      Unit{}
    case False{} True{}:
      match no:
    case True{} _:
      match no:

def no_right(+a: Bool, +b: Bool, no: G.Truth(Bool.not(a || b))) -> G.Truth(Bool.not(b)):
  match a b:
    case False{} False{}:
      Unit{}
    case False{} True{}:
      match no:
    case True{} _:
      match no:

def stationary(+owner: G.Player, +kind: P.PieceKind, +at: Word(6n), +from: Word(6n), +dest: Word(6n),
  +board: P.Position, +turn: G.Player, no: G.Truth(Bool.not(C.equal(at, from)))) -> M.Selected(C.equal(at, from), owner, kind, at, dest, board, turn):
  %Equal.sym(Bool, C.equal(at, from), False{}, no_equal(C.equal(at, from), no)) : M.Selected(_, owner, kind, at, dest, board, turn)
  Unit{}

def empty_selection(+pieces: List<&2, P.Man>, +from: Word(6n), +dest: Word(6n),
  +board: P.Position, +turn: G.Player, +no: G.Truth(Bool.not(C.occupied(pieces, from)))) -> M.Selection(pieces, board, turn, from, dest):
  match pieces:
    case Nil{}:
      Unit{}
    case P.Man{owner, kind, +at} <> +tail:
      (stationary(owner, kind, at, from, dest, board, turn, no_left(C.equal(at, from), C.occupied(tail, from), no)),
        empty_selection(tail, from, dest, board, turn, no_right(C.equal(at, from), C.occupied(tail, from), no)))

def move_occupied(+pieces: List<&2, P.Man>, +board: P.Position, +turn: G.Player, +from: Word(6n), +dest: Word(6n),
  yes: G.Truth(C.piece_move(pieces, board, turn, from, dest))) -> G.Truth(C.occupied(pieces, from)):
  match pieces:
    case Nil{}:
      match yes:
    case P.Man{+owner, +kind, +at} <> +tail:
      Proof.either(G.Truth(C.occupied(pieces, from)),
        Three.same(owner, turn) && C.equal(at, from) && C.geometry(owner, kind, from, dest, board),
        C.piece_move(tail, board, turn, from, dest), yes,
        here => Proof.or_left(C.equal(at, from), C.occupied(tail, from),
          Proof.and_right(Three.same(owner, turn), C.equal(at, from),
            Proof.and_left(Three.same(owner, turn) && C.equal(at, from), C.geometry(owner, kind, from, dest, board), here))),
        there => Proof.or_right(C.equal(at, from), C.occupied(tail, from), move_occupied(tail, board, turn, from, dest, there)))

def geometry_progress(+owner: G.Player, +kind: P.PieceKind, +from: Word(6n), +dest: Word(6n), +board: P.Position,
  yes: G.Truth(C.geometry(owner, kind, from, dest, board))) -> M.PawnProgress(True{}, owner, kind, from, dest):
  match kind:
    case P.Pawn{}:
      Proof.pawn_geometry(owner, from, dest, board, yes)
    case P.Piece{kind}:
      Unit{}

def source_selection(+owner: G.Player, +kind: P.PieceKind, +at: Word(6n), +tail: List<&2, P.Man>,
  +board: P.Position, +turn: G.Player, +from: Word(6n), +dest: Word(6n), same: G.Truth(C.equal(at, from))) ->
  G.Truth(Bool.not(C.occupied(tail, at))) ->
  G.Truth(C.piece_move(P.Man{owner, kind, at} <> tail, board, turn, from, dest)) ->
  M.Selection(P.Man{owner, kind, at} <> tail, board, turn, from, dest):
  %word_reflect(6n, at, from, same) :
    G.Truth(Bool.not(C.occupied(tail, at))) ->
    G.Truth(C.piece_move(P.Man{owner, kind, at} <> tail, board, turn, _, dest)) ->
    M.Selection(P.Man{owner, kind, at} <> tail, board, turn, _, dest)
  %Equal.sym(Bool, C.equal(at, at), True{}, word_refl(6n, at)) :
    G.Truth(Bool.not(C.occupied(tail, at))) ->
    G.Truth((Three.same(owner, turn) && _ && C.geometry(owner, kind, at, dest, board)) || C.piece_move(tail, board, turn, at, dest)) ->
    (M.Selected(_, owner, kind, at, dest, board, turn) & M.Selection(tail, board, turn, at, dest))
  +absent => selected =>
    (Proof.either(M.Selected(True{}, owner, kind, at, dest, board, turn),
      Three.same(owner, turn) && True{} && C.geometry(owner, kind, at, dest, board), C.piece_move(tail, board, turn, at, dest), selected,
      +here => and_intro(Three.same(owner, turn), C.geometry(owner, kind, at, dest, board),
        Proof.and_left(Three.same(owner, turn), True{}, Proof.and_left(Three.same(owner, turn) && True{}, C.geometry(owner, kind, at, dest, board), here)),
        Proof.and_right(Three.same(owner, turn) && True{}, C.geometry(owner, kind, at, dest, board), here)),
      there => contradiction(M.Selected(True{}, owner, kind, at, dest, board, turn), C.occupied(tail, at),
        move_occupied(tail, board, turn, at, dest, there), absent)),
      empty_selection(tail, at, dest, board, turn, absent))

def skip_source(+owner: G.Player, +kind: P.PieceKind, +at: Word(6n), +tail: List<&2, P.Man>,
  +board: P.Position, +turn: G.Player, +from: Word(6n), +dest: Word(6n), no: G.Truth(Bool.not(C.equal(at, from)))) ->
  G.Truth(C.piece_move(P.Man{owner, kind, at} <> tail, board, turn, from, dest)) -> G.Truth(C.piece_move(tail, board, turn, from, dest)):
  %Equal.sym(Bool, C.equal(at, from), False{}, no_equal(C.equal(at, from), no)) :
    G.Truth((Three.same(owner, turn) && _ && C.geometry(owner, kind, from, dest, board)) || C.piece_move(tail, board, turn, from, dest)) ->
    G.Truth(C.piece_move(tail, board, turn, from, dest))
  selected => Proof.either(G.Truth(C.piece_move(tail, board, turn, from, dest)),
    Three.same(owner, turn) && False{} && C.geometry(owner, kind, from, dest, board), C.piece_move(tail, board, turn, from, dest), selected,
    impossible => contradiction(G.Truth(C.piece_move(tail, board, turn, from, dest)), False{},
      Proof.and_right(Three.same(owner, turn), False{},
        Proof.and_left(Three.same(owner, turn) && False{}, C.geometry(owner, kind, from, dest, board), impossible)), Unit{}),
    later => later)

def piece_selection(+pieces: List<&2, P.Man>, +wk: Word(6n), +bk: Word(6n), +board: P.Position,
  +turn: G.Player, +from: Word(6n), +dest: Word(6n), +distinct: G.Truth(C.distinct(pieces, wk, bk)),
  +selected: G.Truth(C.piece_move(pieces, board, turn, from, dest))) -> M.Selection(pieces, board, turn, from, dest):
  match pieces:
    case Nil{}:
      match selected:
    case P.Man{+owner, +kind, +at} <> +tail:
      +head = Bool.not(C.equal(at, wk)) && Bool.not(C.equal(at, bk)) && Bool.not(C.occupied(tail, at))
      split(M.Selection(pieces, board, turn, from, dest), C.equal(at, from),
        same => source_selection(owner, kind, at, tail, board, turn, from, dest, same)(
          Proof.and_right(Bool.not(C.equal(at, wk)) && Bool.not(C.equal(at, bk)), Bool.not(C.occupied(tail, at)),
            Proof.and_left(head, C.distinct(tail, wk, bk), distinct)))(selected),
        +no => (stationary(owner, kind, at, from, dest, board, turn, no),
          piece_selection(tail, wk, bk, board, turn, from, dest,
            Proof.and_right(head, C.distinct(tail, wk, bk), distinct),
            skip_source(owner, kind, at, tail, board, turn, from, dest, no)(selected))))

def not_or(+a: Bool, +b: Bool, left: G.Truth(Bool.not(a)), right: G.Truth(Bool.not(b))) -> G.Truth(Bool.not(a || b)):
  match a b:
    case False{} False{}:
      Unit{}
    case True{} _:
      match left:
    case False{} True{}:
      match right:

def king_square(+turn: G.Player, wk: Word(6n), bk: Word(6n)) -> Word(6n):
  C.king(P.Position{turn, wk, bk, Nil{}, False{}, Word.zero(6n)}, turn)

def king_head(+turn: G.Player, +at: Word(6n), +wk: Word(6n), +bk: Word(6n),
  white: G.Truth(Bool.not(C.equal(at, wk))), black: G.Truth(Bool.not(C.equal(at, bk)))) ->
  G.Truth(Bool.not(C.equal(at, king_square(turn, wk, bk)))):
  match turn:
    case G.White{}:
      white
    case G.Black{}:
      black

def king_empty(+pieces: List<&2, P.Man>, +turn: G.Player, +wk: Word(6n), +bk: Word(6n),
  +distinct: G.Truth(C.distinct(pieces, wk, bk))) -> G.Truth(Bool.not(C.occupied(pieces, king_square(turn, wk, bk)))):
  match pieces:
    case Nil{}:
      Unit{}
    case P.Man{owner, kind, +at} <> +tail:
      +a = Bool.not(C.equal(at, wk))
      +b = Bool.not(C.equal(at, bk))
      +c = Bool.not(C.occupied(tail, at))
      +d = C.distinct(tail, wk, bk)
      +both = Proof.and_left(a && b, c, Proof.and_left(a && b && c, d, distinct))
      not_or(C.equal(at, king_square(turn, wk, bk)), C.occupied(tail, king_square(turn, wk, bk)),
        king_head(turn, at, wk, bk, Proof.and_left(a, b, both), Proof.and_right(a, b, both)),
        king_empty(tail, turn, wk, bk, Proof.and_right(a && b && c, d, distinct)))

def king_selection(+pieces: List<&2, P.Man>, +from: Word(6n), +dest: Word(6n), +king: Word(6n),
  +board: P.Position, +turn: G.Player, same: G.Truth(C.equal(from, king))) -> G.Truth(Bool.not(C.occupied(pieces, king))) -> M.Selection(pieces, board, turn, from, dest):
  %Equal.sym(Word(6n), from, king, word_reflect(6n, from, king, same)) :
    G.Truth(Bool.not(C.occupied(pieces, king))) -> M.Selection(pieces, board, turn, _, dest)
  absent => empty_selection(pieces, king, dest, board, turn, absent)

def king_same(+turn: G.Player, +wk: Word(6n), +bk: Word(6n), +pieces: List<&2, P.Man>, +ep: Bool, +target: Word(6n)) ->
  {C.king(P.Position{turn, wk, bk, pieces, ep, target}, turn) == king_square(turn, wk, bk) : Word(6n)}:
  match turn:
    case G.White{}:
      {==}
    case G.Black{}:
      {==}

def king_empty_board(+turn: G.Player, +wk: Word(6n), +bk: Word(6n), +pieces: List<&2, P.Man>, +ep: Bool, +target: Word(6n),
  distinct: G.Truth(C.distinct(pieces, wk, bk))) -> G.Truth(Bool.not(C.occupied(pieces, C.king(P.Position{turn, wk, bk, pieces, ep, target}, turn)))):
  %Equal.sym(Word(6n), C.king(P.Position{turn, wk, bk, pieces, ep, target}, turn), king_square(turn, wk, bk),
    king_same(turn, wk, bk, pieces, ep, target)) : G.Truth(Bool.not(C.occupied(pieces, _)))
  king_empty(pieces, turn, wk, bk, distinct)

def legal_distinct(+board: P.Position, +move: C.Action, +legal: G.Truth(C.legal(board, move))) ->
  G.Truth(C.valid_plain(board)):
  Proof.and_left(C.valid_plain(board), C.valid_rights(board),
    Proof.and_left(C.valid(board), C.pseudo(board, move),
      Proof.and_left(C.valid(board) && C.pseudo(board, move), C.valid(C.after(board, move)), legal)))

def legal_selection(+board: P.Position, +move: C.Action, +legal: G.Truth(C.legal(board, move))) -> M.MoveSelection(board, move):
  match board move:
    case P.Position{+turn, +wk, +bk, +pieces, ep, target} C.Action{+from, +dest, choice}:
      +distinct = Proof.and_right(Bool.not(C.equal(wk, bk)), C.distinct(pieces, wk, bk),
        Proof.and_left(Bool.not(C.equal(wk, bk)) && C.distinct(pieces, wk, bk), C.ranks(pieces),
          Proof.and_left(Bool.not(C.equal(wk, bk)) && C.distinct(pieces, wk, bk) && C.ranks(pieces),
            Bool.not(C.checked(board, Three.other(turn))), legal_distinct(board, move, legal))))
      +king_move = C.equal(from, C.king(board, turn)) && Geometry.king_step(Three.number(6n, from), Three.number(6n, dest))
      +piece_move = C.piece_move(pieces, board, turn, from, dest)
      selected = Proof.and_right(Bool.not(C.equal(dest, wk)) && Bool.not(C.equal(dest, bk)) && Bool.not(C.friendly(pieces, turn, dest)),
        king_move || piece_move,
        Proof.and_right(C.valid(board), C.pseudo(board, move),
          Proof.and_left(C.valid(board) && C.pseudo(board, move), C.valid(C.after(board, move)), legal)))
      Proof.either(M.Selection(pieces, board, turn, from, dest), king_move, piece_move, selected,
        king => king_selection(pieces, from, dest, C.king(board, turn), board, turn,
          Proof.and_left(C.equal(from, C.king(board, turn)), Geometry.king_step(Three.number(6n, from), Three.number(6n, dest)), king))(
            king_empty_board(turn, wk, bk, pieces, ep, target, distinct)),
        piece => piece_selection(pieces, wk, bk, board, turn, from, dest, distinct, piece))

def selected_progress(+moving: Bool, +owner: G.Player, +kind: P.PieceKind, +at: Word(6n), +dest: Word(6n), +board: P.Position, +turn: G.Player,
  selected: M.Selected(moving, owner, kind, at, dest, board, turn)) -> M.PawnProgress(moving, owner, kind, at, dest):
  match moving:
    case False{}:
      Unit{}
    case True{}:
      geometry_progress(owner, kind, at, dest, board, Proof.and_right(Three.same(owner, turn), C.geometry(owner, kind, at, dest, board), selected))

def selection_progress(+pieces: List<&2, P.Man>, +board: P.Position, +turn: G.Player, +from: Word(6n), +dest: Word(6n),
  selected: M.Selection(pieces, board, turn, from, dest)) -> M.Progress(pieces, from, dest):
  match pieces selected:
    case Nil{} Unit{}:
      Unit{}
    case P.Man{owner, kind, +at} <> tail Tuple{head, rest}:
      (selected_progress(C.equal(at, from), owner, kind, at, dest, board, turn, head), selection_progress(tail, board, turn, from, dest, rest))

def move_progress(+board: P.Position, +move: C.Action, selected: M.MoveSelection(board, move)) -> M.MoveProgress(board, move):
  match board move:
    case P.Position{turn, wk, bk, pieces, ep, target} C.Action{from, dest, choice}:
      selection_progress(pieces, board, turn, from, dest, selected)

def legal_reset(+board: P.Position, +move: C.Action, legal: G.Truth(C.legal(board, move)),
  reset: G.Truth(C.resets(board, move))) -> M.Lt(M.position(C.after(board, move)), M.position(board)):
  Proof.after_reset(board, move, move_progress(board, move, legal_selection(board, move, legal)), reset)

def quiet_pawn(+moving: Bool, +owner: G.Player, +at: Word(6n), +dest: Word(6n), +board: P.Position, +turn: G.Player,
  selected: M.Selected(moving, owner, P.Pawn{}, at, dest, board, turn),
  no: G.Truth(Bool.not(Three.same(owner, turn) && moving))) -> G.Truth(Bool.not(moving)):
  match moving:
    case False{}:
      Unit{}
    case True{}:
      contradiction(Empty, Three.same(owner, turn) && True{},
        and_intro(Three.same(owner, turn), True{}, Proof.and_left(Three.same(owner, turn), C.geometry(owner, P.Pawn{}, at, dest, board), selected), Unit{}), no)

def selection_quiet(+pieces: List<&2, P.Man>, +board: P.Position, +turn: G.Player, +from: Word(6n), +dest: Word(6n),
  selected: M.Selection(pieces, board, turn, from, dest), +no: G.Truth(Bool.not(C.pawn_at(pieces, turn, from)))) ->
  G.Truth(Bool.not(M.pawns_moving(pieces, from))):
  match pieces selected:
    case Nil{} Unit{}:
      Unit{}
    case P.Man{+owner, P.Pawn{}, +at} <> +tail Tuple{head, rest}:
      not_or(C.equal(at, from), M.pawns_moving(tail, from),
        quiet_pawn(C.equal(at, from), owner, at, dest, board, turn, head,
          no_left(Three.same(owner, turn) && C.equal(at, from), C.pawn_at(tail, turn, from), no)),
        selection_quiet(tail, board, turn, from, dest, rest,
          no_right(Three.same(owner, turn) && C.equal(at, from), C.pawn_at(tail, turn, from), no)))
    case P.Man{owner, P.Piece{kind}, at} <> tail Tuple{head, rest}:
      selection_quiet(tail, board, turn, from, dest, rest, no)

def quiet_weight(+moving: Bool, +owner: G.Player, +kind: P.PieceKind, +at: Word(6n), +dest: Word(6n), +choice: Three.Material,
  no: G.Truth(Bool.not(M.moving_pawn(moving, kind)))) ->
  {M.weight(M.moved(moving, owner, kind, at, dest, choice)) == M.weight(P.Man{owner, kind, at}) : Nat}:
  match moving kind:
    case False{} P.Pawn{}:
      {==}
    case True{} P.Pawn{}:
      match no:
    case False{} P.Piece{kind}:
      {==}
    case True{} P.Piece{kind}:
      {==}

def quiet_keep(+remove: Bool, +next: P.Man, +old: P.Man, +tail: List<&2, P.Man>, +before: Nat,
  no: G.Truth(Bool.not(remove)), same: {M.weight(next) == M.weight(old) : Nat}, rest: {M.men(tail) == before : Nat}) ->
  {M.men(C.keep(remove || False{}, next, tail)) == Nat.add(M.weight(old), before) : Nat}:
  match remove:
    case True{}:
      match no:
    case False{}:
      %same : {Nat.add(M.weight(next), M.men(tail)) == Nat.add(_, before) : Nat}
      %rest : {Nat.add(M.weight(next), M.men(tail)) == Nat.add(M.weight(next), _) : Nat}
      {==}

def quiet_update(+pieces: List<&2, P.Man>, +from: Word(6n), +dest: Word(6n), +choice: Three.Material, +victim: Word(6n),
  +no_pawn: G.Truth(Bool.not(M.pawns_moving(pieces, from))), +no_capture: G.Truth(Bool.not(C.occupied(pieces, dest)))) ->
  {M.men(C.move_men(pieces, from, dest, choice, False{}, victim)) == M.men(pieces) : Nat}:
  match pieces:
    case Nil{}:
      {==}
    case P.Man{+owner, +kind, +at} <> +tail:
      quiet_keep(C.equal(at, dest), M.moved(C.equal(at, from), owner, kind, at, dest, choice), P.Man{owner, kind, at},
        C.move_men(tail, from, dest, choice, False{}, victim), M.men(tail),
        no_left(C.equal(at, dest), C.occupied(tail, dest), no_capture),
        quiet_weight(C.equal(at, from), owner, kind, at, dest, choice, no_left(M.moving_pawn(C.equal(at, from), kind), M.pawns_moving(tail, from), no_pawn)),
        quiet_update(tail, from, dest, choice, victim,
          no_right(M.moving_pawn(C.equal(at, from), kind), M.pawns_moving(tail, from), no_pawn),
          no_right(C.equal(at, dest), C.occupied(tail, dest), no_capture)))

def and_false(+a: Bool, +b: Bool, +c: Bool) -> {a && False{} && b && c == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def no_ep(+board: P.Position, +move: C.Action, no: G.Truth(Bool.not(C.pawn_move(board, move)))) -> {C.ep_move(board, move) == False{} : Bool}:
  match board move:
    case P.Position{turn, wk, bk, pieces, +ep, target} C.Action{from, +dest, choice}:
      %Equal.sym(Bool, C.pawn_move(board, move), False{}, no_equal(C.pawn_move(board, move), no)) :
        {ep && _ && C.equal(target, dest) && C.empty(board, dest) == False{} : Bool}
      and_false(ep, C.equal(target, dest), C.empty(board, dest))

def selected_quiet(+board: P.Position, +move: C.Action, selected: M.MoveSelection(board, move),
  +quiet: G.Truth(Bool.not(C.resets(board, move)))) -> {M.position(C.after(board, move)) == M.position(board) : Nat}:
  match board move:
    case P.Position{+turn, wk, bk, +pieces, ep, target} C.Action{+from, +dest, +choice}:
      +no_pawn = no_left(C.pawn_move(board, move), C.occupied(pieces, dest), quiet)
      %Equal.sym(Bool, C.ep_move(board, move), False{}, no_ep(board, move, no_pawn)) :
        {2n+M.men(C.move_men(pieces, from, dest, choice, _, C.shift(Three.other(turn), dest))) == 2n+M.men(pieces) : Nat}
      Equal.cong(Nat, Nat, n => 2n+n, M.men(C.move_men(pieces, from, dest, choice, False{}, C.shift(Three.other(turn), dest))), M.men(pieces),
        quiet_update(pieces, from, dest, choice, C.shift(Three.other(turn), dest),
          selection_quiet(pieces, board, turn, from, dest, selected, no_pawn), no_right(C.pawn_move(board, move), C.occupied(pieces, dest), quiet)))

def legal_quiet(+board: P.Position, +move: C.Action, legal: G.Truth(C.legal(board, move)),
  quiet: G.Truth(Bool.not(C.resets(board, move)))) -> {M.position(C.after(board, move)) == M.position(board) : Nat}:
  selected_quiet(board, move, legal_selection(board, move, legal), quiet)

def reset_step(+limit: Nat, +remaining: Nat, +board: P.Position, +move: C.Action,
  legal: G.Truth(C.legal(board, move)), +reset: G.Truth(C.resets(board, move))) ->
  M.Lt(M.budget(limit, M.position(C.after(board, move)), Bool.pick(Nat, C.resets(board, move), limit, remaining)),
    M.budget(limit, M.position(board), 1n+remaining)):
  %Equal.sym(Bool, C.resets(board, move), True{}, yes_equal(C.resets(board, move), reset)) :
    M.Lt(M.budget(limit, M.position(C.after(board, move)), Bool.pick(Nat, _, limit, remaining)), M.budget(limit, M.position(board), 1n+remaining))
  Proof.reset_budget(limit, M.position(C.after(board, move)), M.position(board), 1n+remaining, legal_reset(board, move, legal, reset))

def quiet_step(+limit: Nat, +remaining: Nat, +board: P.Position, +move: C.Action,
  legal: G.Truth(C.legal(board, move)), +quiet: G.Truth(Bool.not(C.resets(board, move)))) ->
  M.Lt(M.budget(limit, M.position(C.after(board, move)), Bool.pick(Nat, C.resets(board, move), limit, remaining)),
    M.budget(limit, M.position(board), 1n+remaining)):
  %Equal.sym(Bool, C.resets(board, move), False{}, no_equal(C.resets(board, move), quiet)) :
    M.Lt(M.budget(limit, M.position(C.after(board, move)), Bool.pick(Nat, _, limit, remaining)), M.budget(limit, M.position(board), 1n+remaining))
  %Equal.sym(Nat, M.position(C.after(board, move)), M.position(board), legal_quiet(board, move, legal, quiet)) :
    M.Lt(M.budget(limit, _, remaining), M.budget(limit, M.position(board), 1n+remaining))
  Proof.quiet_budget(limit, M.position(board), remaining)

# Every legal continuation from a live clock decreases a natural number.
# With limit=100, resets replenish 100 halfmoves; quiet moves consume one.
def legal_budget(+limit: Nat, +remaining: Nat, +board: P.Position, +move: C.Action,
  +legal: G.Truth(C.legal(board, move))) ->
  M.Lt(M.budget(limit, M.position(C.after(board, move)), Bool.pick(Nat, C.resets(board, move), limit, remaining)),
    M.budget(limit, M.position(board), 1n+remaining)):
  split(M.Lt(M.budget(limit, M.position(C.after(board, move)), Bool.pick(Nat, C.resets(board, move), limit, remaining)),
    M.budget(limit, M.position(board), 1n+remaining)), C.resets(board, move),
    reset => reset_step(limit, remaining, board, move, legal, reset),
    quiet => quiet_step(limit, remaining, board, move, legal, quiet))
