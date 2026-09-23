import Base
import ./pawnless_chess.bend as Three
import ./four_index.bend as Index
import ./pawnless_generator.bend as Gen
import ./table_file.bend as FileIO

# The only callers supply Gen.singles(100n, 20n, 12n), so file_with is exactly
# the byte list certified by generated_pawnless_four_wdl_is_fully_correct.
def write_with(+path: String, material: Index.Material, lower: Gen.Bundle<20n>) -> IO(Unit):
  do IO<Unit>:
    IO.print("Generating " ++ path ++ " (64 MiB; 100 clock layers).")
    file : File <- IO.try(File, File.open(path, "w"))
    pair : File & Result<&1, &1, U32 & String, Unit> <-
      File.write_bytes(file, Gen.file_with(100n, 26n, 20n, 12n, material, lower))
    FileIO.finish(pair)
    IO.print("Wrote " ++ path)

def write(path: String, material: Index.Material) -> IO(Unit):
  do IO<Unit>:
    IO.print("Solving generalized three-man capture dependencies.")
    lower : Gen.Bundle<20n> = Gen.singles(100n, 20n, 12n)
    write_with(path, material, lower)

type Spec is Data:
  Spec{name: String, material: Index.Material}

# Unordered pairs suffice because each file contains both color reversals.
# Keep the declared piece order when encoding/probing a file.
def specs() -> List<&2, Spec>:
  [Spec{"kqqk", Index.Material{Three.Queen{}, Three.Queen{}, False{}}},
   Spec{"kqrk", Index.Material{Three.Queen{}, Three.Rook{}, False{}}},
   Spec{"kqbk", Index.Material{Three.Queen{}, Three.Bishop{}, False{}}},
   Spec{"kqnk", Index.Material{Three.Queen{}, Three.Knight{}, False{}}},
   Spec{"krrk", Index.Material{Three.Rook{}, Three.Rook{}, False{}}},
   Spec{"krbk", Index.Material{Three.Rook{}, Three.Bishop{}, False{}}},
   Spec{"krnk", Index.Material{Three.Rook{}, Three.Knight{}, False{}}},
   Spec{"kbbk", Index.Material{Three.Bishop{}, Three.Bishop{}, False{}}},
   Spec{"kbnk", Index.Material{Three.Bishop{}, Three.Knight{}, False{}}},
   Spec{"knnk", Index.Material{Three.Knight{}, Three.Knight{}, False{}}},
   Spec{"kqkq", Index.Material{Three.Queen{}, Three.Queen{}, True{}}},
   Spec{"kqkr", Index.Material{Three.Queen{}, Three.Rook{}, True{}}},
   Spec{"kqkb", Index.Material{Three.Queen{}, Three.Bishop{}, True{}}},
   Spec{"kqkn", Index.Material{Three.Queen{}, Three.Knight{}, True{}}},
   Spec{"krkr", Index.Material{Three.Rook{}, Three.Rook{}, True{}}},
   Spec{"krkb", Index.Material{Three.Rook{}, Three.Bishop{}, True{}}},
   Spec{"krkn", Index.Material{Three.Rook{}, Three.Knight{}, True{}}},
   Spec{"kbkb", Index.Material{Three.Bishop{}, Three.Bishop{}, True{}}},
   Spec{"kbkn", Index.Material{Three.Bishop{}, Three.Knight{}, True{}}},
   Spec{"knkn", Index.Material{Three.Knight{}, Three.Knight{}, True{}}}]

def batch(specs: List<&2, Spec>, +directory: String, +lower: Gen.Bundle<20n>) -> IO(Unit):
  match specs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Spec{name, material} <> tail:
      do IO<Unit>:
        write_with(directory ++ "/" ++ name ++ ".wdl", material, lower)
        batch(tail, directory, lower)

def all(directory: String) -> IO(Unit):
  do IO<Unit>:
    IO.print("Generating 20 pawnless four-man tables. Capture dependencies are shared.")
    lower : Gen.Bundle<20n> = Gen.singles(100n, 20n, 12n)
    batch(specs(), directory, lower)
