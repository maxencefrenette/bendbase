import Base
import ./src/pawnless_chess.bend as Chess
import ./src/table_file.bend as TableFile

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("Generating pawnless WDL tables (clock zero, one signed byte per position).")
    TableFile.write("build/kqk.wdl", Chess.Queen{})
    IO.print("Wrote build/kqk.wdl")
    TableFile.write("build/krk.wdl", Chess.Rook{})
    IO.print("Wrote build/krk.wdl")
    TableFile.write("build/kbk.wdl", Chess.Bishop{})
    IO.print("Wrote build/kbk.wdl")
    TableFile.write("build/knk.wdl", Chess.Knight{})
    IO.print("Wrote build/knk.wdl")
