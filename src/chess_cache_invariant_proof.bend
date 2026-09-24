import Base
import ./chess_cache_invariant.bend as I
import ./position.bend as P
import ./position_address.bend as Address
import ./chess_measure.bend as M
import ./chess_component.bend as Component
import ./chess_cache.bend as Cache
import ./chess_cache_proof.bend as CacheProof
import ./chess_solver.bend as Compile
import ./component_cache.bend as Stages
import ./component_cache_proof.bend as StageProof
import ./material_cache.bend as Registry
import ./chess_selection_proof.bend as Selection
import ./material_directory_proof.bend as DirectoryProof
import ./game.bend as Game
import ./chess.bend as Chess
import ./chess_graph.bend as Graph
import ./chess_component_proof.bend as ComponentProof
import ./chess_measure_proof.bend as MeasureProof
import ./clock_solver.bend as Solver

def empty_position(~expected: P.Position -> Game.Outcome, +address: Address.Address, position: P.Position,
  bounded: M.Le(M.position(position), 0n)) ->
  {Cache.resolve(Nil{}, address) == Some{expected(Address.position(address))} : Maybe<&2, Game.Outcome>}:
  match position:
    case P.Position{turn, wk, bk, men, ep, target}:
      match bounded:

def empty_address(~expected: P.Position -> Game.Outcome, +capacity: Nat, +address: Address.Address,
  bounded: M.Le(M.position(Address.position(address)), 0n)) ->
  {Cache.resolve(Nil{}, address) == Some{expected(Address.position(address))} : Maybe<&2, Game.Outcome>}:
  empty_position(~expected, address, Address.position(address), bounded)

def empty(~expected: P.Position -> Game.Outcome, +capacity: Nat) -> I.Correct(~expected, 0n, capacity, Nil{}):
  +address => bounded => material => empty_address(~expected, capacity, address, bounded)

def old_read(+query: Nat, +stage: Nat, +entries: List<&2, Registry.Named>, +previous: List<&2, Stages.Stage>, +address: Address.Address,
  different: Game.Truth(Bool.not(Stages.equal(query, stage)))) ->
  {Stages.resolve(Stages.Stage{stage, entries} <> previous, query, address) == Stages.resolve(previous, query, address) : Maybe<&2, Game.Outcome>}:
  %Equal.sym(Bool, Stages.equal(query, stage), False{}, Selection.no_equal(Stages.equal(query, stage), different)) :
    {Stages.read(Stages.choose(_, entries, Stages.find(previous, query)), address) == Stages.resolve(previous, query, address) : Maybe<&2, Game.Outcome>}
  {==}

def current_read(+stage: Nat, +entries: List<&2, Registry.Named>, +previous: List<&2, Stages.Stage>, +address: Address.Address,
  same: {M.position(Address.position(address)) == stage : Nat}) ->
  {Cache.resolve(Stages.Stage{stage, entries} <> previous, address) == Registry.resolve(entries, address) : Maybe<&2, Game.Outcome>}:
  %Equal.sym(Nat, M.position(Address.position(address)), stage, same) :
    {Stages.resolve(Stages.Stage{stage, entries} <> previous, _, address) == Registry.resolve(entries, address) : Maybe<&2, Game.Outcome>}
  Equal.cong(Maybe<&2, List<&2, Registry.Named>>, Maybe<&2, Game.Outcome>, found => Stages.read(found, address),
    Stages.find(Stages.Stage{stage, entries} <> previous, stage), Some{entries}, StageProof.find_head(stage, entries, previous))

# Reset correctness follows from the global induction hypothesis, rather than
# from a registration premise or an independently assumed successor value.
def reset_value(~expected: P.Position -> Game.Outcome,
  +count: Nat, +capacity: Nat, +stages: List<&2, Stages.Stage>, +anchor: Game.Player, +board: P.Position, +move: Chess.Action,
  correct: I.Correct(~expected, count, capacity, stages), legal: Game.Truth(Chess.legal(board, move)), resets: Game.Truth(Chess.resets(board, move)),
  bounded: M.Le(M.position(board), 1n+count), material: M.Le(List.length(&2, P.Descriptor, Component.material(anchor, board)), capacity)) ->
  {Cache.resolve(stages, Graph.address(Graph.route(anchor, board, move))) ==
    Some{expected(Address.position(Graph.address(Graph.route(anchor, board, move))))} : Maybe<&2, Game.Outcome>}:
  +address = Graph.address(Graph.route(anchor, board, move))
  correct(address)(MeasureProof.trans(1n+M.position(Address.position(address)), M.position(board), 1n+count,
    CacheProof.routed_stage(anchor, board, move, legal, resets), bounded))(
    MeasureProof.trans(List.length(&2, P.Descriptor, Component.address_material(address)), List.length(&2, P.Descriptor, Component.material(anchor, board)), capacity,
      ComponentProof.routed_material_count(anchor, board, move), material))

def reset_edge(~expected: P.Position -> Game.Outcome,
  +width: Nat, +count: Nat, +capacity: Nat, +stages: List<&2, Stages.Stage>, +anchor: Game.Player, +board: P.Position, +move: Chess.Action,
  correct: I.Correct(~expected, count, capacity, stages), legal: Game.Truth(Chess.legal(board, move)), resets: Game.Truth(Chess.resets(board, move)),
  bounded: M.Le(M.position(board), 1n+count), material: M.Le(List.length(&2, P.Descriptor, Component.material(anchor, board)), capacity)) ->
  {Cache.reset(width, stages, Graph.address(Graph.route(anchor, board, move))) ==
    Some{Solver.Reset{expected(Address.position(Graph.address(Graph.route(anchor, board, move))))}} : Maybe<&2, Solver.Edge<width>>}:
  Equal.cong(Maybe<&2, Game.Outcome>, Maybe<&2, Solver.Edge<width>>, result => Cache.reset_value(width, result),
    Cache.resolve(stages, Graph.address(Graph.route(anchor, board, move))), Some{expected(Address.position(Graph.address(Graph.route(anchor, board, move))))},
    reset_value(~expected, count, capacity, stages, anchor, board, move, correct, legal, resets, bounded, material))

# A single-use induction hypothesis suffices: an old-stage query uses it
# directly; a current-stage query hands it to the component correctness proof.
def step_at(~expected: P.Position -> Game.Outcome,
  +same: Bool, +count: Nat, +capacity: Nat, +entries: List<&2, Registry.Named>, +previous: List<&2, Stages.Stage>, +address: Address.Address,
  equal: {Stages.equal(M.position(Address.position(address)), 1n+count) == same : Bool},
  bounded: M.Le(M.position(Address.position(address)), 1n+count), material: M.Le(List.length(&2, P.Descriptor, Component.address_material(address)), capacity),
  old: I.Correct(~expected, count, capacity, previous),
  establish: I.Correct(~expected, count, capacity, previous) -> I.Stratum(~expected, 1n+count, capacity, entries)) ->
  {Cache.resolve(Stages.Stage{1n+count, entries} <> previous, address) == Some{expected(Address.position(address))} : Maybe<&2, Game.Outcome>}:
  match same:
    case True{}:
      +at = StageProof.equal_reflect(M.position(Address.position(address)), 1n+count,
        DirectoryProof.matches_true(Stages.equal(M.position(Address.position(address)), 1n+count), equal))
      current = establish(old)
      Equal.trans(Maybe<&2, Game.Outcome>, Cache.resolve(Stages.Stage{1n+count, entries} <> previous, address), Registry.resolve(entries, address), Some{expected(Address.position(address))},
        current_read(1n+count, entries, previous, address, at), current(address)(at)(material))
    case False{}:
      +different = DirectoryProof.matches_false(Stages.equal(M.position(Address.position(address)), 1n+count), equal)
      Equal.trans(Maybe<&2, Game.Outcome>, Cache.resolve(Stages.Stage{1n+count, entries} <> previous, address), Cache.resolve(previous, address), Some{expected(Address.position(address))},
        old_read(M.position(Address.position(address)), 1n+count, entries, previous, address, different),
        old(address)(CacheProof.tighten(M.position(Address.position(address)), 1n+count, bounded, different))(material))

def step(~expected: P.Position -> Game.Outcome,
  +count: Nat, +capacity: Nat, +entries: List<&2, Registry.Named>, +previous: List<&2, Stages.Stage>,
  old: I.Correct(~expected, count, capacity, previous),
  establish: I.Correct(~expected, count, capacity, previous) -> I.Stratum(~expected, 1n+count, capacity, entries)) ->
  I.Correct(~expected, 1n+count, capacity, Stages.Stage{1n+count, entries} <> previous):
  +address => bounded => material =>
    step_at(~expected, Stages.equal(M.position(Address.position(address)), 1n+count), count, capacity, entries, previous, address, {==}, bounded, material, old, establish)

def extend(~expected: P.Position -> Game.Outcome,
  +count: Nat, +capacity: Nat, +entries: List<&2, Registry.Named>, +previous: List<&2, Stages.Stage>,
  old: I.Correct(~expected, count, capacity, previous), current: I.Stratum(~expected, 1n+count, capacity, entries)) ->
  I.Correct(~expected, 1n+count, capacity, Stages.Stage{1n+count, entries} <> previous):
  step(~expected, count, capacity, entries, previous, old, unused => current)
