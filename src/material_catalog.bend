import Base
import ./pawnless_chess.bend as Chess
import ./finite_table.bend as Finite
import ./position.bend as P
import ./material_cache.bend as Registry
import ./table_cache.bend as Cache

def signature(kind: Chess.Material) -> List<&2, P.Descriptor>:
  [P.Descriptor{False{}, P.Piece{kind}}]

# The four non-pawn kinds form an ordinary finite descriptor table. This
# encodes chess promotion choices, not a specialized dependency container.
def pieces() -> Finite.Table(2n, Chess.Material):
  Finite.Fork{Finite.Fork{Chess.Queen{}, Chess.Rook{}}, Finite.Fork{Chess.Bishop{}, Chess.Knight{}}}

def named(entries: Finite.Table(2n, Cache.Entry)) -> List<&2, Registry.Named>:
  Registry.from_family(~Chess.Material, ~signature, 2n, pieces(), entries, Nil{})
