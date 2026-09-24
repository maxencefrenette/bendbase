import Base
import ./pawnless_chess.bend as Chess
import ./finite_table.bend as Finite

# The four non-pawn kinds form an ordinary finite descriptor table. This
# encodes chess promotion choices, not a specialized dependency container.
def pieces() -> Finite.Table(2n, Chess.Material):
  Finite.Fork{Finite.Fork{Chess.Queen{}, Chess.Rook{}}, Finite.Fork{Chess.Bishop{}, Chess.Knight{}}}

def key(kind: Chess.Material) -> Word(2n):
  match kind:
    case Chess.Queen{}:
      WCon{False{}, WCon{False{}, WNil{}}}
    case Chess.Rook{}:
      WCon{False{}, WCon{True{}, WNil{}}}
    case Chess.Bishop{}:
      WCon{True{}, WCon{False{}, WNil{}}}
    case Chess.Knight{}:
      WCon{True{}, WCon{True{}, WNil{}}}

def roundtrip(+kind: Chess.Material) ->
  {Finite.get(2n, Chess.Material, key(kind), pieces()) == kind : Chess.Material}:
  match kind:
    case Chess.Queen{}:
      {==}
    case Chess.Rook{}:
      {==}
    case Chess.Bishop{}:
      {==}
    case Chess.Knight{}:
      {==}
