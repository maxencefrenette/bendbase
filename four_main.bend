import Base
import ./src/pawnless_chess.bend as Three
import ./src/four_index.bend as Index
import ./src/four_file.bend as Files

def kind(text: String) -> Maybe<&2, Three.Material>:
  match text:
    case "q":
      Some{Three.Queen{}}
    case "r":
      Some{Three.Rook{}}
    case "b":
      Some{Three.Bishop{}}
    case "n":
      Some{Three.Knight{}}
    case _:
      None{}

def owners(text: String) -> Maybe<&2, Bool>:
  match text:
    case "same":
      Some{False{}}
    case "opposed":
      Some{True{}}
    case _:
      None{}

def help() -> IO(Unit):
  IO.print("Pawnless four-man WDL generator\nUsage:\n  bendbase-four -- <q|r|b|n> <q|r|b|n> <same|opposed> <output.wdl>\n  bendbase-four -- --all <existing-output-directory>\n  bendbase-four -- --help\n\nOne signed byte per position, 64 MiB per file. Halfmove clock zero.\nNo castling rights. Existing output files are overwritten.\nGeneration speed and peak memory have not been benchmarked.")

def single(first: Maybe<&2, Three.Material>, second: Maybe<&2, Three.Material>, relation: Maybe<&2, Bool>, path: String) -> IO(Unit):
  match first second relation:
    case Some{a} Some{b} Some{opposed}:
      Files.write(path, Index.Material{a, b, opposed})
    case _ _ _:
      IO.die(Unit, 2, "Invalid material. Use q/r/b/n and same/opposed; see --help.")

def run(args: List<String>) -> IO(Unit):
  match args:
    case Nil{}:
      help()
    case "--help" <> Nil{}:
      help()
    case "--all" <> directory <> Nil{}:
      Files.all(directory)
    case first <> second <> relation <> path <> Nil{}:
      single(kind(first), kind(second), owners(relation), path)
    case _:
      IO.die(Unit, 2, "Invalid arguments; see --help.")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    run(args)
