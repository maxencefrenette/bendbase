import Base
import ./game.bend as Game
import ./game_proof.bend as Logic
import ./material_chess.bend as Chess
import ./finite_table.bend as Finite
import ./finite_table_proof.bend as FiniteProof
import ./pawnless_chess.bend as Three
import ./pawnless_index.bend as Index
import ./pawnless_index_proof.bend as IndexProof

def cast(-A: Data, -P: A -> Type, -a: A, -b: A, equality: {a == b : A}, value: P(a)) -> P(b):
  %equality : P(_)
  value

def include_sound(+allowed: Bool, +next: Chess.Position, +tail: List<&2, Chess.Position>, +state: Chess.Position,
  member: Chess.Member(state, Chess.include(allowed, next, tail))) ->
  (Game.Truth(allowed) & {state == next : Chess.Position}) | Chess.Member(state, tail):
  match allowed member:
    case False{} member:
      Inr{member}
    case True{} Inl{equal}:
      Inl{(Unit{}, equal)}
    case True{} Inr{later}:
      Inr{later}

def witness(+width: Nat, +board: Chess.Position, +state: Chess.Position, +key: Word(width),
  evidence: Game.Truth(Chess.legal(board, Chess.action_at(width, key))) &
    {state == Chess.after(board, Chess.action_at(width, key)) : Chess.Position}) -> Chess.LegalSuccessor(width, board, state):
  (key, evidence)

def or_bind(-A: Type, -B: Type, -C: Type, evidence: A | B, f: B -> A | C) -> A | C:
  match evidence:
    case Inl{a}:
      Inl{a}
    case Inr{b}:
      f(b)

def scan_sound(depth: Nat, +width: Nat, +board: Chess.Position,
  +keys: Finite.Table(depth, Word(width)), +tail: List<&2, Chess.Position>, +state: Chess.Position,
  member: Chess.Member(state, Chess.successors.go(depth, width, board, keys, tail))) ->
  Chess.LegalSuccessor(width, board, state) | Chess.Member(state, tail):
  match depth keys:
    case 0n +key:
      Logic.or_map(
        Game.Truth(Chess.legal(board, Chess.action_at(width, key))) &
          {state == Chess.after(board, Chess.action_at(width, key)) : Chess.Position},
        Chess.Member(state, tail), Chess.LegalSuccessor(width, board, state), Chess.Member(state, tail),
        include_sound(Chess.legal(board, Chess.action_at(width, key)), Chess.after(board, Chess.action_at(width, key)), tail, state, member),
        pair => witness(width, board, state, key, pair), later => later)
    case 1n++rest Finite.Fork{+left, +right}:
      or_bind(Chess.LegalSuccessor(width, board, state),
        Chess.Member(state, Chess.successors.go(rest, width, board, right, tail)), Chess.Member(state, tail),
        scan_sound(rest, width, board, left, Chess.successors.go(rest, width, board, right, tail), state, member),
        later => scan_sound(rest, width, board, right, tail, state, later))

def include_tail(+allowed: Bool, +next: Chess.Position, +tail: List<&2, Chess.Position>, +state: Chess.Position,
  member: Chess.Member(state, tail)) -> Chess.Member(state, Chess.include(allowed, next, tail)):
  match allowed:
    case False{}:
      member
    case True{}:
      Inr{member}

def scan_tail(depth: Nat, +width: Nat, +board: Chess.Position,
  +keys: Finite.Table(depth, Word(width)), +tail: List<&2, Chess.Position>, +state: Chess.Position,
  member: Chess.Member(state, tail)) -> Chess.Member(state, Chess.successors.go(depth, width, board, keys, tail)):
  match depth keys:
    case 0n +key:
      include_tail(Chess.legal(board, Chess.action_at(width, key)), Chess.after(board, Chess.action_at(width, key)), tail, state, member)
    case 1n++rest Finite.Fork{+left, +right}:
      scan_tail(rest, width, board, left, Chess.successors.go(rest, width, board, right, tail), state,
        scan_tail(rest, width, board, right, tail, state, member))

def include_complete(+allowed: Bool, +next: Chess.Position, +tail: List<&2, Chess.Position>, yes: Game.Truth(allowed)) ->
  Chess.Member(next, Chess.include(allowed, next, tail)):
  match allowed:
    case False{}:
      match yes:
    case True{}:
      Inl{{==}}

def scan_complete(depth: Nat, +width: Nat, +board: Chess.Position,
  +keys: Finite.Table(depth, Word(width)), +path: Word(depth), +tail: List<&2, Chess.Position>,
  legal: Game.Truth(Chess.legal(board, Chess.action_at(width, Finite.get(depth, Word(width), path, keys))))) ->
  Chess.Member(Chess.after(board, Chess.action_at(width, Finite.get(depth, Word(width), path, keys))),
    Chess.successors.go(depth, width, board, keys, tail)):
  match depth keys path:
    case 0n +key WNil{}:
      include_complete(Chess.legal(board, Chess.action_at(width, key)), Chess.after(board, Chess.action_at(width, key)), tail, legal)
    case 1n++rest Finite.Fork{left, right} WCon{False{}, path}:
      scan_complete(rest, width, board, left, path, Chess.successors.go(rest, width, board, right, tail), legal)
    case 1n++rest Finite.Fork{+left, +right} WCon{True{}, +path}:
      scan_tail(rest, width, board, left, Chess.successors.go(rest, width, board, right, tail),
        Chess.after(board, Chess.action_at(width, Finite.get(rest, Word(width), path, right))),
        scan_complete(rest, width, board, right, path, tail, legal))

def legal_present(+width: Nat, +board: Chess.Position, +key: Word(width),
  legal: Game.Truth(Chess.legal(board, Chess.action_at(width, key)))) ->
  Chess.Member(Chess.after(board, Chess.action_at(width, key)), Chess.successors(width, board)):
  +found = Finite.get(width, Word(width), key, Finite.keys(width))
  +canonical = FiniteProof.keys_get(width, key)
  cast(Word(width), k => Chess.Member(Chess.after(board, Chess.action_at(width, k)), Chess.successors(width, board)),
    found, key, canonical,
    scan_complete(width, width, board, Finite.keys(width), key, Nil{},
      cast(Word(width), k => Game.Truth(Chess.legal(board, Chess.action_at(width, k))),
        key, found, Equal.sym(Word(width), found, key, canonical), legal)))

def no_empty(-A: Type, evidence: A | Empty) -> A:
  match evidence:
    case Inl{value}:
      value
    case Inr{bad}:
      match bad:

def present_legal(+width: Nat, +board: Chess.Position, +state: Chess.Position,
  member: Chess.Member(state, Chess.successors(width, board))) -> Chess.LegalSuccessor(width, board, state):
  no_empty(Chess.LegalSuccessor(width, board, state),
    scan_sound(width, width, board, Finite.keys(width), Nil{}, state, member))

def and_right(+a: Bool, +b: Bool, yes: Game.Truth(a && b)) -> Game.Truth(b):
  match a b:
    case True{} True{}:
      Unit{}
    case True{} False{}:
      match yes:
    case False{} _:
      match yes:

def legal_preserves_valid(+board: Chess.Position, +move: Chess.Action,
  yes: Game.Truth(Chess.legal(board, move))) -> Game.Truth(Chess.valid(Chess.after(board, move))):
  and_right(Chess.valid(board) && Chess.pseudo(board, move), Chess.valid(Chess.after(board, move)), yes)

def witness_valid(+width: Nat, +board: Chess.Position, +next: Chess.Position,
  witness: Chess.LegalSuccessor(width, board, next)) -> Game.Truth(Chess.valid(next)):
  match witness:
    case Tuple{+key, Tuple{legal, equal}}:
      cast(Chess.Position, position => Game.Truth(Chess.valid(position)),
        Chess.after(board, Chess.action_at(width, key)), next,
        Equal.sym(Chess.Position, next, Chess.after(board, Chess.action_at(width, key)), equal),
        legal_preserves_valid(board, Chess.action_at(width, key), legal))

def successor_valid(+width: Nat, +board: Chess.Position, +next: Chess.Position,
  member: Chess.Member(next, Chess.successors(width, board))) -> Game.Truth(Chess.valid(next)):
  witness_valid(width, board, next, present_legal(width, board, next, member))

def action_roundtrip(+move: Chess.Action) -> {Chess.action(Chess.encode(move)) == move : Chess.Action}:
  match move:
    case Chess.Action{WCon{a, WCon{b, WCon{c, WCon{d, WCon{e, WCon{f, WNil{}}}}}}}, dest}:
      {==}

def action_roundtrip_at(+width: Nat, size: {width == 12n : Nat}, +move: Chess.Action) ->
  {Chess.action_at(width, Chess.encode_at(width, move)) == move : Chess.Action}:
  Equal.trans(Chess.Action,
    Chess.action_at(width, Chess.encode_at(width, move)), Chess.action_at(12n, Chess.encode_at(12n, move)), move,
    Equal.cong(Nat, Chess.Action, n => Chess.action_at(n, Chess.encode_at(n, move)), width, 12n, size),
    Equal.trans(Chess.Action, Chess.action_at(12n, Chess.encode_at(12n, move)), Chess.action(Chess.encode(move)), move,
      Equal.cong(Word(12n), Chess.Action, key => Chess.action(key),
        Index.fit(12n, 12n, Index.fit(12n, 12n, Chess.encode(move))), Chess.encode(move),
        Equal.trans(Word(12n), Index.fit(12n, 12n, Index.fit(12n, 12n, Chess.encode(move))),
          Index.fit(12n, 12n, Chess.encode(move)), Chess.encode(move),
          IndexProof.fit_identity(12n, Index.fit(12n, 12n, Chess.encode(move))), IndexProof.fit_identity(12n, Chess.encode(move)))),
      action_roundtrip(move)))

def every_action(+width: Nat, size: {width == 12n : Nat}, +board: Chess.Position, +move: Chess.Action,
  legal: Game.Truth(Chess.legal(board, move))) -> Chess.Member(Chess.after(board, move), Chess.successors(width, board)):
  +decoded = Chess.action_at(width, Chess.encode_at(width, move))
  +equal = action_roundtrip_at(width, size, move)
  cast(Chess.Action, m => Chess.Member(Chess.after(board, m), Chess.successors(width, board)),
    decoded, move, equal,
    legal_present(width, board, Chess.encode_at(width, move),
      cast(Chess.Action, m => Game.Truth(Chess.legal(board, m)), move, decoded,
        Equal.sym(Chess.Action, decoded, move, equal), legal)))

def three_roundtrip(+material: Three.Material, +board: Three.Board) ->
  {Chess.to_three(Chess.from_three(material, board)) == Chess.Single{material, board} : Chess.Projection}:
  match board:
    case Three.Board{owner, turn, wk, bk, pc}:
      {==}
