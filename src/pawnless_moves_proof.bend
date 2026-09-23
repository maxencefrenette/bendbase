import Base
import ./game.bend as Game
import ./game_proof.bend as Logic
import ./pawnless_chess.bend as Chess
import ./finite_table.bend as Finite
import ./finite_table_proof.bend as FiniteProof

def cast(-A: Data, -P: A -> Type, -a: A, -b: A, equality: {a == b : A}, value: P(a)) -> P(b):
  %equality : P(_)
  value

def include_sound(+allowed: Bool, +next: Chess.State, +tail: List<&2, Chess.State>, +state: Chess.State,
  member: Chess.Member(state, Chess.include(allowed, next, tail))) ->
  (Game.Truth(allowed) & {state == next : Chess.State}) | Chess.Member(state, tail):
  match allowed member:
    case False{} member:
      Inr{member}
    case True{} Inl{equal}:
      Inl{(Unit{}, equal)}
    case True{} Inr{later}:
      Inr{later}

def witness(+material: Chess.Material, +board: Chess.Board, +state: Chess.State, +key: Word(7n),
  evidence: Game.Truth(Chess.legal(material, board, Chess.action(key))) &
    {state == Chess.after(board, Chess.action(key)) : Chess.State}) -> Chess.LegalSuccessor(material, board, state):
  (key, evidence)

def or_bind(-A: Type, -B: Type, -C: Type, evidence: A | B, f: B -> A | C) -> A | C:
  match evidence:
    case Inl{a}:
      Inl{a}
    case Inr{b}:
      f(b)

def scan_sound(depth: Nat, +material: Chess.Material, +board: Chess.Board,
  +keys: Finite.Table(depth, Word(7n)), +tail: List<&2, Chess.State>, +state: Chess.State,
  member: Chess.Member(state, Chess.successors.go(depth, material, board, keys, tail))) ->
  Chess.LegalSuccessor(material, board, state) | Chess.Member(state, tail):
  match depth keys:
    case 0n +key:
      Logic.or_map(
        Game.Truth(Chess.legal(material, board, Chess.action(key))) &
          {state == Chess.after(board, Chess.action(key)) : Chess.State},
        Chess.Member(state, tail), Chess.LegalSuccessor(material, board, state), Chess.Member(state, tail),
        include_sound(Chess.legal(material, board, Chess.action(key)), Chess.after(board, Chess.action(key)), tail, state, member),
        pair => witness(material, board, state, key, pair), later => later)
    case 1n++rest Finite.Fork{+left, +right}:
      or_bind(Chess.LegalSuccessor(material, board, state),
        Chess.Member(state, Chess.successors.go(rest, material, board, right, tail)), Chess.Member(state, tail),
        scan_sound(rest, material, board, left, Chess.successors.go(rest, material, board, right, tail), state, member),
        later => scan_sound(rest, material, board, right, tail, state, later))

def include_tail(+allowed: Bool, +next: Chess.State, +tail: List<&2, Chess.State>, +state: Chess.State,
  member: Chess.Member(state, tail)) -> Chess.Member(state, Chess.include(allowed, next, tail)):
  match allowed:
    case False{}:
      member
    case True{}:
      Inr{member}

def scan_tail(depth: Nat, +material: Chess.Material, +board: Chess.Board,
  +keys: Finite.Table(depth, Word(7n)), +tail: List<&2, Chess.State>, +state: Chess.State,
  member: Chess.Member(state, tail)) -> Chess.Member(state, Chess.successors.go(depth, material, board, keys, tail)):
  match depth keys:
    case 0n +key:
      include_tail(Chess.legal(material, board, Chess.action(key)), Chess.after(board, Chess.action(key)), tail, state, member)
    case 1n++rest Finite.Fork{+left, +right}:
      scan_tail(rest, material, board, left, Chess.successors.go(rest, material, board, right, tail), state,
        scan_tail(rest, material, board, right, tail, state, member))

def include_complete(+allowed: Bool, +next: Chess.State, +tail: List<&2, Chess.State>, yes: Game.Truth(allowed)) ->
  Chess.Member(next, Chess.include(allowed, next, tail)):
  match allowed:
    case False{}:
      match yes:
    case True{}:
      Inl{{==}}

def scan_complete(depth: Nat, +material: Chess.Material, +board: Chess.Board,
  +keys: Finite.Table(depth, Word(7n)), +path: Word(depth), +tail: List<&2, Chess.State>,
  legal: Game.Truth(Chess.legal(material, board, Chess.action(Finite.get(depth, Word(7n), path, keys))))) ->
  Chess.Member(Chess.after(board, Chess.action(Finite.get(depth, Word(7n), path, keys))),
    Chess.successors.go(depth, material, board, keys, tail)):
  match depth keys path:
    case 0n +key WNil{}:
      include_complete(Chess.legal(material, board, Chess.action(key)), Chess.after(board, Chess.action(key)), tail, legal)
    case 1n++rest Finite.Fork{left, right} WCon{False{}, path}:
      scan_complete(rest, material, board, left, path, Chess.successors.go(rest, material, board, right, tail), legal)
    case 1n++rest Finite.Fork{+left, +right} WCon{True{}, +path}:
      scan_tail(rest, material, board, left, Chess.successors.go(rest, material, board, right, tail),
        Chess.after(board, Chess.action(Finite.get(rest, Word(7n), path, right))),
        scan_complete(rest, material, board, right, path, tail, legal))

def legal_present(+material: Chess.Material, +board: Chess.Board, +key: Word(7n),
  legal: Game.Truth(Chess.legal(material, board, Chess.action(key)))) ->
  Chess.Member(Chess.after(board, Chess.action(key)), Chess.successors(material, board)):
  +found = Finite.get(7n, Word(7n), key, Finite.keys(7n))
  +canonical = FiniteProof.keys_get(7n, key)
  cast(Word(7n), k => Chess.Member(Chess.after(board, Chess.action(k)), Chess.successors(material, board)),
    found, key, canonical,
    scan_complete(7n, material, board, Finite.keys(7n), key, Nil{},
      cast(Word(7n), k => Game.Truth(Chess.legal(material, board, Chess.action(k))),
        key, found, Equal.sym(Word(7n), found, key, canonical), legal)))

def no_empty(-A: Type, evidence: A | Empty) -> A:
  match evidence:
    case Inl{value}:
      value
    case Inr{bad}:
      match bad:

def present_legal(+material: Chess.Material, +board: Chess.Board, +state: Chess.State,
  member: Chess.Member(state, Chess.successors(material, board))) -> Chess.LegalSuccessor(material, board, state):
  no_empty(Chess.LegalSuccessor(material, board, state),
    scan_sound(7n, material, board, Finite.keys(7n), Nil{}, state, member))
