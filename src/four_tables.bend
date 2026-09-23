import Base
import ./game.bend as Game
import ./four_index.bend as Index
import ./four_solver.bend as Solver
import ./finite_table.bend as Finite
import ./pawnless_tables.bend as Bytes

# Pure reference byte-list definition. No four-man generation is invoked by
# main.bend or PROOF.bend. The clock-layer implementation is pawnless_generator.bend.
def entries(depth: Nat, +width: Nat, +limit: Nat, +moves: Nat, +material: Index.Material,
  keys: Finite.Table(depth, Word(width))) -> Finite.Table(depth, Game.Outcome):
  match depth keys:
    case 0n key:
      Solver.value(limit, moves, Index.position(material, Index.decode_at(width, key)))
    case 1n++rest Finite.Fork{left, right}:
      a b = entries(rest, width, limit, moves, material, left) entries(rest, width, limit, moves, material, right)
      Finite.Fork{a, b}

def generate(+width: Nat, limit: Nat, moves: Nat, material: Index.Material) -> Finite.Table(width, Game.Outcome):
  entries(width, width, limit, moves, material, Finite.keys(width))

def file(+width: Nat, limit: Nat, moves: Nat, material: Index.Material) -> List<&2, U32>:
  Finite.flatten(width, Bytes.bytes(width, generate(width, limit, moves, material)))
