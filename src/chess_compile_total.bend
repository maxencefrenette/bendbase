import Base
import ./chess_solver.bend as Compile
import ./chess_solver_proof.bend as CompileProof
import ./chess.bend as Chess
import ./chess_graph.bend as Graph
import ./chess_component.bend as Component
import ./chess_component_proof.bend as ComponentProof
import ./chess_cache.bend as Cache
import ./chess_measure.bend as Measure
import ./chess_selection_proof.bend as Selection
import ./position.bend as P
import ./position_address.bend as Address
import ./position_index.bend as Index
import ./material_directory.bend as Directory
import ./material_directory_proof.bend as DirectoryProof
import ./component_cache.bend as Stages
import ./clock_solver.bend as Solver
import ./finite_table.bend as Finite
import ./game.bend as Game
import ./pawnless_chess.bend as Three

def Success(-A: Data, +result: Maybe<&2, A>) -> Type:
  &value: A -> {result == Some{value} : Maybe<&2, A>}

def decide(+b: Bool) -> Game.Truth(b) | Game.Truth(Bool.not(b)):
  match b:
    case True{}:
      Inl{Unit{}}
    case False{}:
      Inr{Unit{}}

def key(+source: Nat, +target: Nat, format: {source == target : Nat}) ->
  @+word: Word(source) -> Success(Word(target), Compile.key(source, target, word)):
  %format : @+word: Word(source) -> Success(Word(_), Compile.key(source, _, word))
  +word => (word, CompileProof.key_exact(source, word))

def quiet_found(+width: Nat, +value: Maybe<&2, Word(width)>, found: Success(Word(width), value)) ->
  Success(Solver.Edge<width>, Compile.quiet(width, value)):
  (encoded, exact) = found
  (Solver.Quiet{encoded}, Equal.cong(Maybe<&2, Word(width)>, Maybe<&2, Solver.Edge<width>>, word => Compile.quiet(width, word), value, Some{encoded}, exact))

def quiet(+width: Nat, +stages: List<&2, Stages.Stage>, +address: Address.Address,
  format: {Component.address_width(address) == width : Nat}) ->
  Success(Solver.Edge<width>, Compile.edge(width, stages, Graph.Quiet{address})):
  match address:
    case Address.Address{n, material, word}:
      convert = key(Index.width(n), width, format)
      quiet_found(width, Compile.key(Index.width(n), width, word), convert(word))

def reset(+width: Nat, +stages: List<&2, Stages.Stage>, +address: Address.Address,
  found: Success(Game.Outcome, Cache.resolve(stages, address))) ->
  Success(Solver.Edge<width>, Compile.edge(width, stages, Graph.Reset{address})):
  (value, exact) = found
  (Solver.Reset{value}, Equal.cong(Maybe<&2, Game.Outcome>, Maybe<&2, Solver.Edge<width>>, result => Cache.reset_value(width, result),
    Cache.resolve(stages, address), Some{value}, exact))

def quiet_width(+anchor: Game.Player, +board: P.Position, +move: Chess.Action,
  legal: Game.Truth(Chess.legal(board, move)), +quiet: {Chess.resets(board, move) == False{} : Bool}) ->
  {Component.address_width(Address.of_position(anchor, Chess.after(board, move))) == Component.address_width(Address.of_position(anchor, board)) : Nat}:
  %quiet : {Component.address_width(Graph.address(Graph.edge(_, Address.of_position(anchor, Chess.after(board, move))))) == Component.address_width(Address.of_position(anchor, board)) : Nat}
  ComponentProof.routed_width(anchor, board, move, legal, DirectoryProof.matches_false(Chess.resets(board, move), quiet))

def legal_quiet_at(+stages: List<&2, Stages.Stage>, +anchor: Game.Player, +board: P.Position, +move: Chess.Action,
  legal: Game.Truth(Chess.legal(board, move)), +no_reset: {Chess.resets(board, move) == False{} : Bool}) ->
  Success(Solver.Edge<Component.address_width(Address.of_position(anchor, board))>,
    Compile.edge(Component.address_width(Address.of_position(anchor, board)), stages, Graph.route(anchor, board, move))):
  %Equal.sym(Bool, Chess.resets(board, move), False{}, no_reset) :
    Success(Solver.Edge<Component.address_width(Address.of_position(anchor, board))>,
      Compile.edge(Component.address_width(Address.of_position(anchor, board)), stages, Graph.edge(_, Address.of_position(anchor, Chess.after(board, move)))))
  quiet(Component.address_width(Address.of_position(anchor, board)), stages, Address.of_position(anchor, Chess.after(board, move)),
    quiet_width(anchor, board, move, legal, no_reset))

# The width premise comes from legal quiet-component closure, not from a
# caller-provided assertion about a particular encoded destination.
def legal_quiet(+stages: List<&2, Stages.Stage>, +anchor: Game.Player, +board: P.Position, +move: Chess.Action,
  legal: Game.Truth(Chess.legal(board, move)), no_reset: Game.Truth(Bool.not(Chess.resets(board, move)))) ->
  Success(Solver.Edge<Component.address_width(Address.of_position(anchor, board))>,
    Compile.edge(Component.address_width(Address.of_position(anchor, board)), stages, Graph.route(anchor, board, move))):
  legal_quiet_at(stages, anchor, board, move, legal, Selection.no_equal(Chess.resets(board, move), no_reset))

def reset_address(+stages: List<&2, Stages.Stage>, +anchor: Game.Player, +board: P.Position, +move: Chess.Action,
  resets: {Chess.resets(board, move) == True{} : Bool},
  found: Success(Game.Outcome, Cache.resolve(stages, Graph.address(Graph.route(anchor, board, move))))) ->
  Success(Game.Outcome, Cache.resolve(stages, Address.of_position(anchor, Chess.after(board, move)))):
  %resets : Success(Game.Outcome, Cache.resolve(stages, Graph.address(Graph.edge(_, Address.of_position(anchor, Chess.after(board, move))))))
  found

def reset_route(+width: Nat, +stages: List<&2, Stages.Stage>, +anchor: Game.Player, +board: P.Position, +move: Chess.Action,
  +resets: {Chess.resets(board, move) == True{} : Bool},
  found: Success(Game.Outcome, Cache.resolve(stages, Graph.address(Graph.route(anchor, board, move))))) ->
  Success(Solver.Edge<width>, Compile.edge(width, stages, Graph.route(anchor, board, move))):
  %Equal.sym(Bool, Chess.resets(board, move), True{}, resets) :
    Success(Solver.Edge<width>, Compile.edge(width, stages, Graph.edge(_, Address.of_position(anchor, Chess.after(board, move)))))
  reset(width, stages, Address.of_position(anchor, Chess.after(board, move)), reset_address(stages, anchor, board, move, resets, found))

def legal_case(~C: Data,
  ~solve: @+name: List<&2, P.Descriptor> -> Nat -> C -> List<&2, Stages.Stage> -> Finite.Table(Directory.width(name), Game.Outcome),
  +count: Nat, +capacity: Nat, +context: C, +anchor: Game.Player, +board: P.Position, +move: Chess.Action,
  legal: Game.Truth(Chess.legal(board, move)), bounded: Measure.Le(Measure.position(board), 1n+count),
  material: Measure.Le(List.length(&2, P.Descriptor, Component.material(anchor, board)), capacity),
  decision: Game.Truth(Chess.resets(board, move)) | Game.Truth(Bool.not(Chess.resets(board, move)))) ->
  Success(Solver.Edge<Component.address_width(Address.of_position(anchor, board))>,
    Compile.edge(Component.address_width(Address.of_position(anchor, board)), Directory.schedule(~C, ~solve, count, capacity, context), Graph.route(anchor, board, move))):
  match decision:
    case Inl{+resets}:
      reset_route(Component.address_width(Address.of_position(anchor, board)), Directory.schedule(~C, ~solve, count, capacity, context), anchor, board, move,
        Selection.yes_equal(Chess.resets(board, move), resets),
        DirectoryProof.reset_resolves(~C, ~solve, count, capacity, context, anchor, board, move, legal, resets, bounded, material))
    case Inr{quiet}:
      legal_quiet(Directory.schedule(~C, ~solve, count, capacity, context), anchor, board, move, legal, quiet)

def legal_edge(~C: Data,
  ~solve: @+name: List<&2, P.Descriptor> -> Nat -> C -> List<&2, Stages.Stage> -> Finite.Table(Directory.width(name), Game.Outcome),
  +count: Nat, +capacity: Nat, +context: C, +anchor: Game.Player, +board: P.Position, +move: Chess.Action,
  legal: Game.Truth(Chess.legal(board, move)), bounded: Measure.Le(Measure.position(board), 1n+count),
  material: Measure.Le(List.length(&2, P.Descriptor, Component.material(anchor, board)), capacity)) ->
  Success(Solver.Edge<Component.address_width(Address.of_position(anchor, board))>,
    Compile.edge(Component.address_width(Address.of_position(anchor, board)), Directory.schedule(~C, ~solve, count, capacity, context), Graph.route(anchor, board, move))):
  legal_case(~C, ~solve, count, capacity, context, anchor, board, move, legal, bounded, material, decide(Chess.resets(board, move)))

def cons_equal(+width: Nat, +head: Maybe<&2, Solver.Edge<width>>, +tail: Maybe<&2, List<&2, Solver.Edge<width>>>,
  +h: Solver.Edge<width>, +t: List<&2, Solver.Edge<width>>, hp: {head == Some{h} : Maybe<&2, Solver.Edge<width>>},
  tp: {tail == Some{t} : Maybe<&2, List<&2, Solver.Edge<width>>>}) ->
  {Compile.cons(width, head, tail) == Some{h <> t} : Maybe<&2, List<&2, Solver.Edge<width>>>}:
  %Equal.sym(Maybe<&2, Solver.Edge<width>>, head, Some{h}, hp) : {Compile.cons(width, _, tail) == Some{h <> t} : Maybe<&2, List<&2, Solver.Edge<width>>>}
  %Equal.sym(Maybe<&2, List<&2, Solver.Edge<width>>>, tail, Some{t}, tp) : {Compile.cons(width, Some{h}, _) == Some{h <> t} : Maybe<&2, List<&2, Solver.Edge<width>>>}
  {==}

def cons(+width: Nat, +head: Maybe<&2, Solver.Edge<width>>, +tail: Maybe<&2, List<&2, Solver.Edge<width>>>,
  first: Success(Solver.Edge<width>, head), rest: Success(List<&2, Solver.Edge<width>>, tail)) ->
  Success(List<&2, Solver.Edge<width>>, Compile.cons(width, head, tail)):
  (+h, hp) = first
  (+t, tp) = rest
  (h <> t, cons_equal(width, head, tail, h, t, hp, tp))

def include(~C: Data,
  ~solve: @+name: List<&2, P.Descriptor> -> Nat -> C -> List<&2, Stages.Stage> -> Finite.Table(Directory.width(name), Game.Outcome),
  +allowed: Bool, +count: Nat, +capacity: Nat, +context: C, +anchor: Game.Player, +board: P.Position, +move: Chess.Action, +tail: List<&2, Graph.Edge>,
  decision: {Chess.legal(board, move) == allowed : Bool}, bounded: Measure.Le(Measure.position(board), 1n+count),
  material: Measure.Le(List.length(&2, P.Descriptor, Component.material(anchor, board)), capacity),
  rest: Success(List<&2, Solver.Edge<Component.address_width(Address.of_position(anchor, board))>>,
    Compile.edges(Component.address_width(Address.of_position(anchor, board)), Directory.schedule(~C, ~solve, count, capacity, context), tail))) ->
  Success(List<&2, Solver.Edge<Component.address_width(Address.of_position(anchor, board))>>,
    Compile.edges(Component.address_width(Address.of_position(anchor, board)), Directory.schedule(~C, ~solve, count, capacity, context), Graph.include(allowed, Graph.route(anchor, board, move), tail))):
  match allowed:
    case False{}:
      rest
    case True{}:
      cons(Component.address_width(Address.of_position(anchor, board)),
        Compile.edge(Component.address_width(Address.of_position(anchor, board)), Directory.schedule(~C, ~solve, count, capacity, context), Graph.route(anchor, board, move)),
        Compile.edges(Component.address_width(Address.of_position(anchor, board)), Directory.schedule(~C, ~solve, count, capacity, context), tail),
        legal_edge(~C, ~solve, count, capacity, context, anchor, board, move, DirectoryProof.matches_true(Chess.legal(board, move), decision), bounded, material), rest)

# Bounds are Type-kinded; duplicate their evidence by induction, not by an
# unchecked cast or an assumption that arbitrary proof objects are copyable.
def bounds(a: Nat, b: Nat, proof: Measure.Le(a, b)) -> Measure.Le(a, b) & Measure.Le(a, b):
  match a b:
    case 0n b:
      (Unit{}, Unit{})
    case 1n+a 0n:
      match proof:
    case 1n+a 1n+b:
      bounds(a, b, proof)

def compose(-A: Type, -B: Type, -X: Type, -Y: Type, -Z: Type,
  aa: A & A, bb: B & B, rest: X, first: A -> B -> X -> Y, second: A -> B -> Y -> Z) -> Z:
  (a, a2) = aa
  (b, b2) = bb
  second(a2)(b2)(first(a)(b)(rest))

def Ready(+stages: List<&2, Stages.Stage>, +anchor: Game.Player, +board: P.Position, +children: List<&2, Graph.Edge>) -> Type:
  Success(List<&2, Solver.Edge<Component.address_width(Address.of_position(anchor, board))>>,
    Compile.edges(Component.address_width(Address.of_position(anchor, board)), stages, children))

def scan(~C: Data,
  ~solve: @+name: List<&2, P.Descriptor> -> Nat -> C -> List<&2, Stages.Stage> -> Finite.Table(Directory.width(name), Game.Outcome),
  depth: Nat, +width: Nat, +count: Nat, +capacity: Nat, +context: C, +anchor: Game.Player, +board: P.Position,
  +keys: Finite.Table(depth, Word(width)), +tail: List<&2, Graph.Edge>,
  bounded: Measure.Le(Measure.position(board), 1n+count), material: Measure.Le(List.length(&2, P.Descriptor, Component.material(anchor, board)), capacity),
  rest: Success(List<&2, Solver.Edge<Component.address_width(Address.of_position(anchor, board))>>,
    Compile.edges(Component.address_width(Address.of_position(anchor, board)), Directory.schedule(~C, ~solve, count, capacity, context), tail))) ->
  Success(List<&2, Solver.Edge<Component.address_width(Address.of_position(anchor, board))>>,
    Compile.edges(Component.address_width(Address.of_position(anchor, board)), Directory.schedule(~C, ~solve, count, capacity, context), Graph.scan(depth, width, anchor, board, keys, tail))):
  match depth keys:
    case 0n key:
      include(~C, ~solve, Chess.legal(board, Chess.action_at(width, key)), count, capacity, context, anchor, board, Chess.action_at(width, key), tail, {==}, bounded, material, rest)
    case 1n++smaller Finite.Fork{left, right}:
      +stages = Directory.schedule(~C, ~solve, count, capacity, context)
      compose(Measure.Le(Measure.position(board), 1n+count), Measure.Le(List.length(&2, P.Descriptor, Component.material(anchor, board)), capacity),
        Ready(stages, anchor, board, tail), Ready(stages, anchor, board, Graph.scan(smaller, width, anchor, board, right, tail)),
        Ready(stages, anchor, board, Graph.scan(smaller, width, anchor, board, left, Graph.scan(smaller, width, anchor, board, right, tail))),
        bounds(Measure.position(board), 1n+count, bounded), bounds(List.length(&2, P.Descriptor, Component.material(anchor, board)), capacity, material), rest,
        a => b => ready => scan(~C, ~solve, smaller, width, count, capacity, context, anchor, board, right, tail, a, b, ready),
        a => b => ready => scan(~C, ~solve, smaller, width, count, capacity, context, anchor, board, left, Graph.scan(smaller, width, anchor, board, right, tail), a, b, ready))

def choice(+width: Nat, +turn: Game.Player, +children: Maybe<&2, List<&2, Solver.Edge<width>>>,
  ready: Success(List<&2, Solver.Edge<width>>, children)) -> Success(Solver.Node<width>, Compile.choice(width, turn, children)):
  (+values, exact) = ready
  (Solver.Choice{turn, values}, Equal.cong(Maybe<&2, List<&2, Solver.Edge<width>>>, Maybe<&2, Solver.Node<width>>,
    list => Compile.choice(width, turn, list), children, Some{values}, exact))

def moves(+width: Nat, +stages: List<&2, Stages.Stage>, +board: P.Position, +children: List<&2, Graph.Edge>,
  ready: Success(List<&2, Solver.Edge<width>>, Compile.edges(width, stages, children))) ->
  Success(Solver.Node<width>, Compile.node(width, stages, Graph.node.moves(board, children))):
  match board children:
    case P.Position{turn, wk, bk, men, ep, target} Nil{}:
      (Solver.Terminal{Three.mate(Chess.checked(board, turn), turn)}, {==})
    case P.Position{turn, wk, bk, men, ep, target} head <> tail:
      choice(width, turn, Compile.edges(width, stages, head <> tail), ready)

def live(~C: Data,
  ~solve: @+name: List<&2, P.Descriptor> -> Nat -> C -> List<&2, Stages.Stage> -> Finite.Table(Directory.width(name), Game.Outcome),
  +allowed: Bool, +actions: Nat, +count: Nat, +capacity: Nat, +context: C, +anchor: Game.Player, +board: P.Position,
  bounded: Measure.Le(Measure.position(board), 1n+count), material: Measure.Le(List.length(&2, P.Descriptor, Component.material(anchor, board)), capacity)) ->
  Success(Solver.Node<Component.address_width(Address.of_position(anchor, board))>,
    Compile.node(Component.address_width(Address.of_position(anchor, board)), Directory.schedule(~C, ~solve, count, capacity, context), Graph.node.live(allowed, actions, anchor, board))):
  match allowed:
    case False{}:
      (Solver.Terminal{Game.Draw{}}, {==})
    case True{}:
      moves(Component.address_width(Address.of_position(anchor, board)), Directory.schedule(~C, ~solve, count, capacity, context), board, Graph.successors(actions, anchor, board),
        scan(~C, ~solve, actions, actions, count, capacity, context, anchor, board, Finite.keys(actions), Nil{}, bounded, material, (Nil{}, {==})))

# Every chess node compiles against a sufficiently completed total schedule.
# This uses only source bounds: neither per-edge availability nor compiler
# success is a premise. The schedule's arbitrary values need not yet be WDL.
def node(~C: Data,
  ~solve: @+name: List<&2, P.Descriptor> -> Nat -> C -> List<&2, Stages.Stage> -> Finite.Table(Directory.width(name), Game.Outcome),
  +actions: Nat, +count: Nat, +capacity: Nat, +context: C, +anchor: Game.Player, +board: P.Position,
  bounded: Measure.Le(Measure.position(board), 1n+count), material: Measure.Le(List.length(&2, P.Descriptor, Component.material(anchor, board)), capacity)) ->
  Success(Solver.Node<Component.address_width(Address.of_position(anchor, board))>,
    Compile.node(Component.address_width(Address.of_position(anchor, board)), Directory.schedule(~C, ~solve, count, capacity, context), Graph.node(actions, anchor, board))):
  match board:
    case P.Position{turn, wk, bk, men, ep, target}:
      live(~C, ~solve, Chess.valid(board) && Bool.not(Chess.insufficient(men)), actions, count, capacity, context, anchor, board, bounded, material)
