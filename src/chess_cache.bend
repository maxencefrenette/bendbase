import Base
import ./game.bend as Game
import ./position_address.bend as Address
import ./chess_measure.bend as Measure
import ./component_cache.bend as Stages
import ./clock_solver.bend as Solver

# The chess position, not a material-specific adapter, determines the stage.
# A missing stage, material, or exact-width table remains an explicit failure.
def resolve(stages: List<&2, Stages.Stage>, +address: Address.Address) -> Maybe<&2, Game.Outcome>:
  Stages.resolve(stages, Measure.position(Address.position(address)), address)

def reset_value(-width: Nat, result: Maybe<&2, Game.Outcome>) -> Maybe<&2, Solver.Edge<width>>:
  match result:
    case None{}:
      None{}
    case Some{value}:
      Some{Solver.Reset{value}}

def reset(+width: Nat, stages: List<&2, Stages.Stage>, address: Address.Address) -> Maybe<&2, Solver.Edge<width>>:
  reset_value(width, resolve(stages, address))
