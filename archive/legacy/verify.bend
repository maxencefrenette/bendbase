import Base
import ./src/input.bend as Input
import ./src/pawn.bend as Pawn
import ./src/certificate.bend as Certificate

def result.if(valid: Bool) -> IO(Unit):
  match valid:
    case True{}:
      IO.print("All five table files are certified.")
    case False{}:
      IO.die(Unit, 1, "table file certificate failed")

def result(checked: (Pawn.Promoted & Array<U32>) & Bool) -> IO(Unit):
  match checked:
    case (tables, valid):
      result.if(valid)

def main() -> IO(Unit):
  do IO<Unit>:
    queen : Array<U32> <- Input.read("build/kqk.wdl")
    rook : Array<U32> <- Input.read("build/krk.wdl")
    bishop : Array<U32> <- Input.read("build/kbk.wdl")
    knight : Array<U32> <- Input.read("build/knk.wdl")
    pawn : Array<U32> <- Input.read("build/kpk.wdl")
    result(Certificate.all((Pawn.Promoted{queen, rook, bishop, knight}, pawn)))
