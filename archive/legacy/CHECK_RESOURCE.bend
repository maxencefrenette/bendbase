import Base
import ./src/resource_wdl_spec.bend as Resource
import ./src/rules.bend as Rules

law pawn_identity:
  for +push_rest: Nat
  for +clock_rest: Nat
  for +squares: List<&2, U32>
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for x: Resource.Pawn(1n+push_rest,
    1n+clock_rest, squares,
    Rules.State{wk, bk, pc, 0})
  Resource.Pawn(1n+push_rest,
    1n+clock_rest, squares,
    Rules.State{wk, bk, pc, 0})

def pawn_identity(push_rest, clock_rest,
  squares, wk, bk, pc, x):
  x
