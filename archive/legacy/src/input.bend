import Base

def load.go(fuel: Nat, +i: U32, xs: List<&2, U32>,
  table: Array<U32>) -> Maybe<Array<U32>>:
  match fuel xs:
    case 0n Nil{}:
      Some{table}
    case 0n Con{h, t}:
      None{}
    case 1n+rest Nil{}:
      None{}
    case 1n+rest Con{value, tail}:
      table[i] <- value
      load.go(rest, (i + 1 : U32), tail, table)

def load(xs: List<&2, U32>) -> Maybe<Array<U32>>:
  load.go(524288n, 0, xs, [0 : U32^19n])

def loaded(maybe: Maybe<Array<U32>>) -> IO(Array<U32>):
  match maybe:
    case None{}:
      IO.die(Array<U32>, 1, "table file must contain 524288 bytes")
    case Some{table}:
      IO.pure(Array<U32>, table)

def read.done(pair: File &
  Result<&1, &1, U32 & String, List<&2, U32>>) ->
  IO(List<&2, U32>):
  match pair:
    case (file, result):
      do IO<List<&2, U32>>:
        data : List<&2, U32> <- IO.pass(List<&2, U32>, result)
        File.close(file)
        return data

def read(path: String) -> IO(Array<U32>):
  do IO<Array<U32>>:
    file : File <- IO.try(File, File.open(path, "r"))
    pair : File & Result<&1, &1, U32 & String, List<&2, U32>> <-
      File.read_bytes(file, 524289)
    data : List<&2, U32> <- read.done(pair)
    table : Array<U32> <- loaded(load(data))
    return table
