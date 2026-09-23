import Base
import ./pawn.bend as Pawn
import ./proof_tree.bend as ProofTree

def bytes.go(table: Array<U32>, acc: List<&2, U32>) ->
  List<&2, U32>:
  match table:
    case ALeaf{value}:
      value <> acc
    case ANode{left, right}:
      bytes.go(left, bytes.go(right, acc))

def bytes(table: Array<U32>) -> List<&2, U32>:
  bytes.go(table, Nil{})

def write.done(pair: File & Result<&1, &1, U32 & String, Unit>) ->
  IO(Unit):
  match pair:
    case (file, result):
      do IO<Unit>:
        IO.pass(Unit, result)
        File.close(file)

def write(path: String, table: Array<U32>) -> IO(Unit):
  do IO<Unit>:
    file : File <- IO.try(File, File.open(path, "w"))
    pair : File & Result<&1, &1, U32 & String, Unit> <-
      File.write_bytes(file, bytes(table))
    write.done(pair)

def all.pieces(promoted: Pawn.Promoted, pawn: Array<U32>) -> IO(Unit):
  match promoted:
    case Pawn.Promoted{queen, rook, bishop, knight}:
      do IO<Unit>:
        write("build/kqk.wdl", queen)
        write("build/krk.wdl", rook)
        write("build/kbk.wdl", bishop)
        write("build/knk.wdl", knight)
        write("build/kpk.wdl", pawn)

def all(pair: Pawn.Promoted & Array<U32>) -> IO(Unit):
  match pair:
    case (promoted, pawn):
      all.pieces(promoted, pawn)

# The proof-first generator writes the proven tree order directly. Its leaves
# are already bytes (0 for draw, 1 for White win); no Array conversion occurs
# between the certified value and the file writer.
def write_tree(path: String, tree: ProofTree.Tree) -> IO(Unit):
  do IO<Unit>:
    file : File <- IO.try(File, File.open(path, "w"))
    pair : File & Result<&1, &1, U32 & String, Unit> <-
      File.write_bytes(file, ProofTree.bytes(tree))
    write.done(pair)

def all_trees(queen: ProofTree.Tree,
  rook: ProofTree.Tree,
  pawn: ProofTree.Tree) -> IO(Unit):
  do IO<Unit>:
    write_tree("build/kqk.wdl", queen)
    write_tree("build/krk.wdl", rook)
    write_tree("build/kbk.wdl", ProofTree.filled(19n, 0))
    write_tree("build/knk.wdl", ProofTree.filled(19n, 0))
    write_tree("build/kpk.wdl", pawn)
