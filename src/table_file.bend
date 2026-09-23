import Base
import ./pawnless_chess.bend as Chess
import ./pawnless_tables.bend as Tables
import ./pawn_tables.bend as PawnTables

# The pure byte list here is exactly the list certified by LAWS.bend.
# File IO and the Bend runtime are the ordinary trusted execution boundary.
def finish(pair: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  match pair:
    case Tuple{file, result}:
      do IO<Unit>:
        IO.pass(Unit, result)
        File.close(file)

def write(path: String, material: Chess.Material) -> IO(Unit):
  do IO<Unit>:
    file : File <- IO.try(File, File.open(path, "w"))
    pair : File & Result<&1, &1, U32 & String, Unit> <-
      File.write_bytes(file, Tables.file(100n, 20n, material))
    finish(pair)

def write_kpk(path: String) -> IO(Unit):
  do IO<Unit>:
    file : File <- IO.try(File, File.open(path, "w"))
    pair : File & Result<&1, &1, U32 & String, Unit> <-
      File.write_bytes(file, PawnTables.file(100n, 20n))
    finish(pair)
