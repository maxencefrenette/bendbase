import Base
import ./position.bend as P
import ./position_index.bend as Index
import ./chess_solver.bend as Compile
import ./chess_game.bend as ChessGame
import ./material_directory.bend as Directory
import ./material_cache.bend as Registry
import ./finite_table.bend as Finite
import ./table_engine.bend as Engine
import ./game.bend as Game

# Correctness-first COMMON generator for arbitrary ordered material. It
# directly tabulates the chess game, with no assumed reset-table correctness.
# This is deliberately not a performance implementation. The clock/cache
# pipeline remains separate until its equivalence proof is completed.
def position(+name: List<&2, P.Descriptor>, key: Word(Directory.width(name))) -> P.Position:
  P.position(List.length(&2, P.Descriptor, name), Compile.material(name), Index.decode(List.length(&2, P.Descriptor, name), key))

def value(+name: List<&2, P.Descriptor>, +limit: Nat, key: Word(Directory.width(name))) -> Game.Outcome:
  Game.evaluate(ChessGame.tree(limit, limit, position(name, key)))

def fill(depth: Nat, +name: List<&2, P.Descriptor>, +limit: Nat,
  keys: Finite.Table(depth, Word(Directory.width(name)))) -> Finite.Table(depth, Game.Outcome):
  match depth keys:
    case 0n key:
      value(name, limit, key)
    case 1n++rest Finite.Fork{left, right}:
      a b = fill(rest, name, limit, left) fill(rest, name, limit, right)
      Finite.Fork{a, b}

def table(+name: List<&2, P.Descriptor>, limit: Nat) -> Finite.Table(Directory.width(name), Game.Outcome):
  fill(Directory.width(name), name, limit, Finite.keys(Directory.width(name)))

def generate(capacity: Nat, limit: Nat) -> List<&2, Registry.Named>:
  Directory.build(~Nat, ~table, capacity, limit)

# One byte per full internal key, including EP continuations. No compression
# or new filesystem format is claimed; legacy file-writing entrypoints remain.
def file(+name: List<&2, P.Descriptor>, limit: Nat) -> List<&2, U32>:
  Finite.flatten(Directory.width(name), Engine.bytes(Directory.width(name), table(name, limit)))
