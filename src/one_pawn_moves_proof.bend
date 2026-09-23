import Base
import ./game.bend as Game
import ./game_proof.bend as Logic
import ./one_pawn_chess.bend as Chess
import ./finite_table.bend as Finite
import ./finite_table_proof.bend as FiniteProof
import ./pawnless_chess.bend as Three
import ./pawnless_index.bend as Index
import ./pawnless_index_proof.bend as IndexProof
import ./material_moves_proof.bend as MaterialProof

def cast(-A: Data, -P: A -> Type, -a: A, -b: A, equality: {a == b : A}, value: P(a)) -> P(b):
  %equality : P(_)
  value

def include_sound(+allowed: Bool, +next: Chess.Edge, +tail: List<&2, Chess.Edge>, +state: Chess.Edge,
  member: Chess.Member(state, Chess.include(allowed, next, tail))) ->
  (Game.Truth(allowed) & {state == next : Chess.Edge}) | Chess.Member(state, tail):
  match allowed member:
    case False{} member:
      Inr{member}
    case True{} Inl{equal}:
      Inl{(Unit{}, equal)}
    case True{} Inr{later}:
      Inr{later}

def witness(+width: Nat, +advance: Nat, +board: Chess.Position, +state: Chess.Edge, +key: Word(width),
  evidence: Game.Truth(Chess.legal(advance, board, Chess.action_at(width, key))) &
    {state == Chess.after(advance, board, Chess.action_at(width, key)) : Chess.Edge}) -> Chess.LegalSuccessor(width, advance, board, state):
  (key, evidence)

def or_bind(-A: Type, -B: Type, -C: Type, evidence: A | B, f: B -> A | C) -> A | C:
  match evidence:
    case Inl{a}:
      Inl{a}
    case Inr{b}:
      f(b)

def scan_sound(depth: Nat, +width: Nat, +advance: Nat, +board: Chess.Position,
  +keys: Finite.Table(depth, Word(width)), +tail: List<&2, Chess.Edge>, +state: Chess.Edge,
  member: Chess.Member(state, Chess.successors.go(depth, width, advance, board, keys, tail))) ->
  Chess.LegalSuccessor(width, advance, board, state) | Chess.Member(state, tail):
  match depth keys:
    case 0n +key:
      Logic.or_map(
        Game.Truth(Chess.legal(advance, board, Chess.action_at(width, key))) &
          {state == Chess.after(advance, board, Chess.action_at(width, key)) : Chess.Edge},
        Chess.Member(state, tail), Chess.LegalSuccessor(width, advance, board, state), Chess.Member(state, tail),
        include_sound(Chess.legal(advance, board, Chess.action_at(width, key)), Chess.after(advance, board, Chess.action_at(width, key)), tail, state, member),
        pair => witness(width, advance, board, state, key, pair), later => later)
    case 1n++rest Finite.Fork{+left, +right}:
      or_bind(Chess.LegalSuccessor(width, advance, board, state),
        Chess.Member(state, Chess.successors.go(rest, width, advance, board, right, tail)), Chess.Member(state, tail),
        scan_sound(rest, width, advance, board, left, Chess.successors.go(rest, width, advance, board, right, tail), state, member),
        later => scan_sound(rest, width, advance, board, right, tail, state, later))

def include_tail(+allowed: Bool, +next: Chess.Edge, +tail: List<&2, Chess.Edge>, +state: Chess.Edge,
  member: Chess.Member(state, tail)) -> Chess.Member(state, Chess.include(allowed, next, tail)):
  match allowed:
    case False{}:
      member
    case True{}:
      Inr{member}

def scan_tail(depth: Nat, +width: Nat, +advance: Nat, +board: Chess.Position,
  +keys: Finite.Table(depth, Word(width)), +tail: List<&2, Chess.Edge>, +state: Chess.Edge,
  member: Chess.Member(state, tail)) -> Chess.Member(state, Chess.successors.go(depth, width, advance, board, keys, tail)):
  match depth keys:
    case 0n +key:
      include_tail(Chess.legal(advance, board, Chess.action_at(width, key)), Chess.after(advance, board, Chess.action_at(width, key)), tail, state, member)
    case 1n++rest Finite.Fork{+left, +right}:
      scan_tail(rest, width, advance, board, left, Chess.successors.go(rest, width, advance, board, right, tail), state,
        scan_tail(rest, width, advance, board, right, tail, state, member))

def include_complete(+allowed: Bool, +next: Chess.Edge, +tail: List<&2, Chess.Edge>, yes: Game.Truth(allowed)) ->
  Chess.Member(next, Chess.include(allowed, next, tail)):
  match allowed:
    case False{}:
      match yes:
    case True{}:
      Inl{{==}}

def scan_complete(depth: Nat, +width: Nat, +advance: Nat, +board: Chess.Position,
  +keys: Finite.Table(depth, Word(width)), +path: Word(depth), +tail: List<&2, Chess.Edge>,
  legal: Game.Truth(Chess.legal(advance, board, Chess.action_at(width, Finite.get(depth, Word(width), path, keys))))) ->
  Chess.Member(Chess.after(advance, board, Chess.action_at(width, Finite.get(depth, Word(width), path, keys))),
    Chess.successors.go(depth, width, advance, board, keys, tail)):
  match depth keys path:
    case 0n +key WNil{}:
      include_complete(Chess.legal(advance, board, Chess.action_at(width, key)), Chess.after(advance, board, Chess.action_at(width, key)), tail, legal)
    case 1n++rest Finite.Fork{left, right} WCon{False{}, path}:
      scan_complete(rest, width, advance, board, left, path, Chess.successors.go(rest, width, advance, board, right, tail), legal)
    case 1n++rest Finite.Fork{+left, +right} WCon{True{}, +path}:
      scan_tail(rest, width, advance, board, left, Chess.successors.go(rest, width, advance, board, right, tail),
        Chess.after(advance, board, Chess.action_at(width, Finite.get(rest, Word(width), path, right))),
        scan_complete(rest, width, advance, board, right, path, tail, legal))

def legal_present(+width: Nat, +advance: Nat, +board: Chess.Position, +key: Word(width),
  legal: Game.Truth(Chess.legal(advance, board, Chess.action_at(width, key)))) ->
  Chess.Member(Chess.after(advance, board, Chess.action_at(width, key)), Chess.successors(width, advance, board)):
  +found = Finite.get(width, Word(width), key, Finite.keys(width))
  +canonical = FiniteProof.keys_get(width, key)
  cast(Word(width), k => Chess.Member(Chess.after(advance, board, Chess.action_at(width, k)), Chess.successors(width, advance, board)),
    found, key, canonical,
    scan_complete(width, width, advance, board, Finite.keys(width), key, Nil{},
      cast(Word(width), k => Game.Truth(Chess.legal(advance, board, Chess.action_at(width, k))),
        key, found, Equal.sym(Word(width), found, key, canonical), legal)))

def no_empty(-A: Type, evidence: A | Empty) -> A:
  match evidence:
    case Inl{value}:
      value
    case Inr{bad}:
      match bad:

def present_legal(+width: Nat, +advance: Nat, +board: Chess.Position, +state: Chess.Edge,
  member: Chess.Member(state, Chess.successors(width, advance, board))) -> Chess.LegalSuccessor(width, advance, board, state):
  no_empty(Chess.LegalSuccessor(width, advance, board, state),
    scan_sound(width, width, advance, board, Finite.keys(width), Nil{}, state, member))

def action_roundtrip(+move: Chess.Action) -> {Chess.action(Chess.encode(move)) == move : Chess.Action}:
  match move:
    case Chess.King{dest}:
      {==}
    case Chess.Piece{dest}:
      {==}
    case Chess.Step{file}:
      {==}
    case Chess.Double{}:
      {==}
    case Chess.Promote{file, Three.Queen{}}:
      {==}
    case Chess.Promote{file, Three.Rook{}}:
      {==}
    case Chess.Promote{file, Three.Bishop{}}:
      {==}
    case Chess.Promote{file, Three.Knight{}}:
      {==}
    case Chess.Unused{}:
      {==}

def action_roundtrip_at(+width: Nat, size: {width == 8n : Nat}, +move: Chess.Action) ->
  {Chess.action_at(width, Chess.encode_at(width, move)) == move : Chess.Action}:
  Equal.trans(Chess.Action,
    Chess.action_at(width, Chess.encode_at(width, move)), Chess.action_at(8n, Chess.encode_at(8n, move)), move,
    Equal.cong(Nat, Chess.Action, n => Chess.action_at(n, Chess.encode_at(n, move)), width, 8n, size),
    Equal.trans(Chess.Action, Chess.action_at(8n, Chess.encode_at(8n, move)), Chess.action(Chess.encode(move)), move,
      Equal.cong(Word(8n), Chess.Action, key => Chess.action(key),
        Index.fit(8n, 8n, Index.fit(8n, 8n, Chess.encode(move))), Chess.encode(move),
        Equal.trans(Word(8n), Index.fit(8n, 8n, Index.fit(8n, 8n, Chess.encode(move))),
          Index.fit(8n, 8n, Chess.encode(move)), Chess.encode(move),
          IndexProof.fit_identity(8n, Index.fit(8n, 8n, Chess.encode(move))), IndexProof.fit_identity(8n, Chess.encode(move)))),
      action_roundtrip(move)))

def every_action(+width: Nat, size: {width == 8n : Nat}, +advance: Nat, +board: Chess.Position, +move: Chess.Action,
  legal: Game.Truth(Chess.legal(advance, board, move))) -> Chess.Member(Chess.after(advance, board, move), Chess.successors(width, advance, board)):
  +decoded = Chess.action_at(width, Chess.encode_at(width, move))
  +equal = action_roundtrip_at(width, size, move)
  cast(Chess.Action, m => Chess.Member(Chess.after(advance, board, m), Chess.successors(width, advance, board)),
    decoded, move, equal,
    legal_present(width, advance, board, Chess.encode_at(width, move),
      cast(Chess.Action, m => Game.Truth(Chess.legal(advance, board, m)), move, decoded,
        Equal.sym(Chess.Action, decoded, move, equal), legal)))

def legal_safe(+advance: Nat, +board: Chess.Position, +move: Chess.Action,
  legal: Game.Truth(Chess.legal(advance, board, move))) -> Game.Truth(Chess.safe(advance, Chess.after(advance, board, move))):
  MaterialProof.and_right(Chess.valid(advance, board) && Chess.pseudo(advance, board, move),
    Chess.safe(advance, Chess.after(advance, board, move)), legal)

def witness_safe(+width: Nat, +advance: Nat, +board: Chess.Position, +next: Chess.Edge,
  witness: Chess.LegalSuccessor(width, advance, board, next)) -> Game.Truth(Chess.safe(advance, next)):
  match witness:
    case Tuple{+key, Tuple{legal, equal}}:
      cast(Chess.Edge, edge => Game.Truth(Chess.safe(advance, edge)),
        Chess.after(advance, board, Chess.action_at(width, key)), next,
        Equal.sym(Chess.Edge, next, Chess.after(advance, board, Chess.action_at(width, key)), equal),
        legal_safe(advance, board, Chess.action_at(width, key), legal))

def successor_safe(+width: Nat, +advance: Nat, +board: Chess.Position, +next: Chess.Edge,
  member: Chess.Member(next, Chess.successors(width, advance, board))) -> Game.Truth(Chess.safe(advance, next)):
  witness_safe(width, advance, board, next, present_legal(width, advance, board, next, member))
