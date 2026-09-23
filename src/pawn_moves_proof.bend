import Base
import ./game.bend as Game
import ./game_proof.bend as Logic
import ./pawn_chess.bend as Pawn
import ./finite_table.bend as Finite
import ./finite_table_proof.bend as FiniteProof

def cast(-A: Data, -P: A -> Type, -a: A, -b: A, equality: {a == b : A}, value: P(a)) -> P(b):
  %equality : P(_)
  value

def include_sound(+allowed: Bool, +next: Pawn.Edge, +tail: List<&2, Pawn.Edge>, +state: Pawn.Edge,
  member: Pawn.Member(state, Pawn.include(allowed, next, tail))) ->
  (Game.Truth(allowed) & {state == next : Pawn.Edge}) | Pawn.Member(state, tail):
  match allowed member:
    case False{} member:
      Inr{member}
    case True{} Inl{equal}:
      Inl{(Unit{}, equal)}
    case True{} Inr{later}:
      Inr{later}

def witness(+advance: Nat, +board: Pawn.Position, +state: Pawn.Edge, +key: Word(7n),
  evidence: Game.Truth(Pawn.legal(advance, board, Pawn.action(key))) &
    {state == Pawn.after(advance, board, Pawn.action(key)) : Pawn.Edge}) -> Pawn.LegalSuccessor(advance, board, state):
  (key, evidence)

def or_bind(-A: Type, -B: Type, -C: Type, evidence: A | B, f: B -> A | C) -> A | C:
  match evidence:
    case Inl{a}:
      Inl{a}
    case Inr{b}:
      f(b)

def scan_sound(depth: Nat, +advance: Nat, +board: Pawn.Position,
  +keys: Finite.Table(depth, Word(7n)), +tail: List<&2, Pawn.Edge>, +state: Pawn.Edge,
  member: Pawn.Member(state, Pawn.successors.go(depth, advance, board, keys, tail))) ->
  Pawn.LegalSuccessor(advance, board, state) | Pawn.Member(state, tail):
  match depth keys:
    case 0n +key:
      Logic.or_map(
        Game.Truth(Pawn.legal(advance, board, Pawn.action(key))) &
          {state == Pawn.after(advance, board, Pawn.action(key)) : Pawn.Edge},
        Pawn.Member(state, tail), Pawn.LegalSuccessor(advance, board, state), Pawn.Member(state, tail),
        include_sound(Pawn.legal(advance, board, Pawn.action(key)), Pawn.after(advance, board, Pawn.action(key)), tail, state, member),
        pair => witness(advance, board, state, key, pair), later => later)
    case 1n++rest Finite.Fork{+left, +right}:
      or_bind(Pawn.LegalSuccessor(advance, board, state),
        Pawn.Member(state, Pawn.successors.go(rest, advance, board, right, tail)), Pawn.Member(state, tail),
        scan_sound(rest, advance, board, left, Pawn.successors.go(rest, advance, board, right, tail), state, member),
        later => scan_sound(rest, advance, board, right, tail, state, later))

def include_tail(+allowed: Bool, +next: Pawn.Edge, +tail: List<&2, Pawn.Edge>, +state: Pawn.Edge,
  member: Pawn.Member(state, tail)) -> Pawn.Member(state, Pawn.include(allowed, next, tail)):
  match allowed:
    case False{}:
      member
    case True{}:
      Inr{member}

def scan_tail(depth: Nat, +advance: Nat, +board: Pawn.Position,
  +keys: Finite.Table(depth, Word(7n)), +tail: List<&2, Pawn.Edge>, +state: Pawn.Edge,
  member: Pawn.Member(state, tail)) -> Pawn.Member(state, Pawn.successors.go(depth, advance, board, keys, tail)):
  match depth keys:
    case 0n +key:
      include_tail(Pawn.legal(advance, board, Pawn.action(key)), Pawn.after(advance, board, Pawn.action(key)), tail, state, member)
    case 1n++rest Finite.Fork{+left, +right}:
      scan_tail(rest, advance, board, left, Pawn.successors.go(rest, advance, board, right, tail), state,
        scan_tail(rest, advance, board, right, tail, state, member))

def include_complete(+allowed: Bool, +next: Pawn.Edge, +tail: List<&2, Pawn.Edge>, yes: Game.Truth(allowed)) ->
  Pawn.Member(next, Pawn.include(allowed, next, tail)):
  match allowed:
    case False{}:
      match yes:
    case True{}:
      Inl{{==}}

def scan_complete(depth: Nat, +advance: Nat, +board: Pawn.Position,
  +keys: Finite.Table(depth, Word(7n)), +path: Word(depth), +tail: List<&2, Pawn.Edge>,
  legal: Game.Truth(Pawn.legal(advance, board, Pawn.action(Finite.get(depth, Word(7n), path, keys))))) ->
  Pawn.Member(Pawn.after(advance, board, Pawn.action(Finite.get(depth, Word(7n), path, keys))),
    Pawn.successors.go(depth, advance, board, keys, tail)):
  match depth keys path:
    case 0n +key WNil{}:
      include_complete(Pawn.legal(advance, board, Pawn.action(key)), Pawn.after(advance, board, Pawn.action(key)), tail, legal)
    case 1n++rest Finite.Fork{left, right} WCon{False{}, path}:
      scan_complete(rest, advance, board, left, path, Pawn.successors.go(rest, advance, board, right, tail), legal)
    case 1n++rest Finite.Fork{+left, +right} WCon{True{}, +path}:
      scan_tail(rest, advance, board, left, Pawn.successors.go(rest, advance, board, right, tail),
        Pawn.after(advance, board, Pawn.action(Finite.get(rest, Word(7n), path, right))),
        scan_complete(rest, advance, board, right, path, tail, legal))

def legal_present(+advance: Nat, +board: Pawn.Position, +key: Word(7n),
  legal: Game.Truth(Pawn.legal(advance, board, Pawn.action(key)))) ->
  Pawn.Member(Pawn.after(advance, board, Pawn.action(key)), Pawn.successors(advance, board)):
  +found = Finite.get(7n, Word(7n), key, Finite.keys(7n))
  +canonical = FiniteProof.keys_get(7n, key)
  cast(Word(7n), k => Pawn.Member(Pawn.after(advance, board, Pawn.action(k)), Pawn.successors(advance, board)),
    found, key, canonical,
    scan_complete(7n, advance, board, Finite.keys(7n), key, Nil{},
      cast(Word(7n), k => Game.Truth(Pawn.legal(advance, board, Pawn.action(k))),
        key, found, Equal.sym(Word(7n), found, key, canonical), legal)))

def no_empty(-A: Type, evidence: A | Empty) -> A:
  match evidence:
    case Inl{value}:
      value
    case Inr{bad}:
      match bad:

def present_legal(+advance: Nat, +board: Pawn.Position, +state: Pawn.Edge,
  member: Pawn.Member(state, Pawn.successors(advance, board))) -> Pawn.LegalSuccessor(advance, board, state):
  no_empty(Pawn.LegalSuccessor(advance, board, state),
    scan_sound(7n, advance, board, Finite.keys(7n), Nil{}, state, member))
