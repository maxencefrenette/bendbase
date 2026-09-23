import Base
import ./src/clocked_tables.bend as Tables
import ./src/output.bend as Output

# The generator follows the clock-layer and pawn-budget recursions proved in
# PROOF.bend. Output.all writes one file per material class.
def main() -> IO(Unit):
  +queen = Tables.nonpawn(0)
  +rook = Tables.nonpawn(1)
  +pawn = Tables.pawn(queen, rook)
  do IO<Unit>:
    Output.all_trees(queen, rook, pawn)
    IO.print("Wrote all five three-man WDL tables.")
