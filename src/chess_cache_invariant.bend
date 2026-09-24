import Base
import ./position.bend as P
import ./position_address.bend as Address
import ./chess_component.bend as Component
import ./chess_measure.bend as Measure
import ./chess_cache.bend as Cache
import ./component_cache.bend as Stages
import ./material_cache.bend as Registry
import ./game.bend as Game
import ./chess_solver.bend as Compile
import ./material_directory.bend as Directory

# Parametric in the chess meaning, not in a table or cache evaluator. This
# separates the cache bookkeeping theorem from the chess/clock induction.
# The function must eventually be instantiated with proved chess semantics;
# arbitrary expected values alone do not establish WDL correctness.
def Correct(~expected: P.Position -> Game.Outcome,
  +count: Nat, +capacity: Nat, +stages: List<&2, Stages.Stage>) -> Type:
  @+address: Address.Address ->
  Measure.Le(Measure.position(Address.position(address)), count) ->
  Measure.Le(List.length(&2, P.Descriptor, Component.address_material(address)), capacity) ->
  {Cache.resolve(stages, address) == Some{expected(Address.position(address))} : Maybe<&2, Game.Outcome>}

# Only the live positions in this measure stratum are constrained. Padding
# entries are intentionally unconstrained, and every address retains EP state.
def Stratum(~expected: P.Position -> Game.Outcome,
  +stage: Nat, +capacity: Nat, +entries: List<&2, Registry.Named>) -> Type:
  @+address: Address.Address ->
  {Measure.position(Address.position(address)) == stage : Nat} ->
  Measure.Le(List.length(&2, P.Descriptor, Component.address_material(address)), capacity) ->
  {Registry.resolve(entries, address) == Some{expected(Address.position(address))} : Maybe<&2, Game.Outcome>}

# The remaining local semantic obligation. It concerns the actual component
# directory builder, not an arbitrary cache extension or a reference solver.
# Fix the clock limit before choosing expected: WDL need not agree between
# different limits. This obligation belongs to the cached alternative only.
def StageRule(~expected: P.Position -> Game.Outcome, +limit: Nat) -> Type:
  @+count: Nat -> @+capacity: Nat ->
  @+previous: List<&2, Stages.Stage> -> @+entries: List<&2, Registry.Named> ->
  Correct(~expected, count, capacity, previous) ->
  {Compile.directory(Directory.names(capacity), 1n+count, limit, previous) == Some{entries} : Maybe<&2, List<&2, Registry.Named>>} ->
  Stratum(~expected, 1n+count, capacity, entries)
