import Base
import ./position.bend as P
import ./chess_tables.bend as Tables
import ./table_file.bend as Files

# One material signature per file; one signed-WDL byte per full internal key.
# The byte list is proved below the normal trusted File.write_bytes boundary.
# This unoptimized generator is opt-in: never invoked by the existing mains.
def write(path: String, name: List<&2, P.Descriptor>) -> IO(Unit):
  do IO<Unit>:
    file : File <- IO.try(File, File.open(path, "w"))
    pair : File & Result<&1, &1, U32 & String, Unit> <-
      File.write_bytes(file, Tables.file(name, 100n))
    Files.finish(pair)
