import Base
import ../src/position.bend as P
import ../src/pawnless_chess.bend as Three
import ../src/chess_table_file.bend as Files

# Opt-in benchmark entrypoint for the correctness-first common generator.
# Each signature covers both anchor colors and both sides to move. Keep all
# timing/resource limits outside the generator so its workload is unchanged.
def run(args: List<String>) -> IO(Unit):
  match args:
    case "q" <> path <> Nil{}:
      Files.write(path, [P.Descriptor{False{}, P.Piece{Three.Queen{}}}])
    case "r" <> path <> Nil{}:
      Files.write(path, [P.Descriptor{False{}, P.Piece{Three.Rook{}}}])
    case "b" <> path <> Nil{}:
      Files.write(path, [P.Descriptor{False{}, P.Piece{Three.Bishop{}}}])
    case "n" <> path <> Nil{}:
      Files.write(path, [P.Descriptor{False{}, P.Piece{Three.Knight{}}}])
    case "p" <> path <> Nil{}:
      Files.write(path, [P.Descriptor{False{}, P.Pawn{}}])
    case _:
      IO.die(Unit, 2, "Usage: bench-three -- <q|r|b|n|p> <output.wdl>")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    run(args)
