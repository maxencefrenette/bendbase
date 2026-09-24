import Base
import ./chess_tables.bend as Tables
import ./chess_game.bend as ChessGame
import ./position.bend as P
import ./material_directory.bend as Directory
import ./material_directory_proof.bend as DirectoryProof
import ./material_cache.bend as Registry
import ./table_cache.bend as Cache
import ./table_cache_proof.bend as CacheProof
import ./chess_measure.bend as Measure
import ./chess_measure_proof.bend as MeasureProof
import ./finite_table.bend as Finite
import ./finite_table_proof.bend as FiniteProof
import ./table_engine.bend as Engine
import ./table_engine_proof.bend as EngineProof
import ./game.bend as Game
import ./game_proof.bend as GameProof

def fill(+depth: Nat, +name: List<&2, P.Descriptor>, +limit: Nat,
  +keys: Finite.Table(depth, Word(Directory.width(name))), +key: Word(depth)) ->
  {Finite.get(depth, Game.Outcome, key, Tables.fill(depth, name, limit, keys)) ==
    Tables.value(name, limit, Finite.get(depth, Word(Directory.width(name)), key, keys)) : Game.Outcome}:
  match depth keys key:
    case 0n original WNil{}:
      {==}
    case 1n+rest Finite.Fork{left, right} WCon{False{}, tail}:
      fill(rest, name, limit, left, tail)
    case 1n+rest Finite.Fork{left, right} WCon{True{}, tail}:
      fill(rest, name, limit, right, tail)

def table(+name: List<&2, P.Descriptor>, +limit: Nat, +key: Word(Directory.width(name))) ->
  {Finite.get(Directory.width(name), Game.Outcome, key, Tables.table(name, limit)) ==
    Game.evaluate(ChessGame.tree(limit, limit, Tables.position(name, key))) : Game.Outcome}:
  %FiniteProof.keys_get(Directory.width(name), key) :
    {Finite.get(Directory.width(name), Game.Outcome, key, Tables.table(name, limit)) == Tables.value(name, limit, _) : Game.Outcome}
  fill(Directory.width(name), name, limit, Finite.keys(Directory.width(name)), key)

def directory(+capacity: Nat, +limit: Nat, +name: List<&2, P.Descriptor>, bounded: Measure.Le(List.length(&2, P.Descriptor, name), capacity)) ->
  {Registry.find(Tables.generate(capacity, limit), name) == Some{Cache.Entry{Directory.width(name), Tables.table(name, limit)}} : Maybe<&2, Cache.Entry>}:
  DirectoryProof.build(~Nat, ~Tables.table, capacity, name, limit, bounded)

def lookup(+capacity: Nat, +limit: Nat, +name: List<&2, P.Descriptor>, +key: Word(Directory.width(name)), bounded: Measure.Le(List.length(&2, P.Descriptor, name), capacity)) ->
  {Registry.lookup(Tables.generate(capacity, limit), name, Directory.width(name), key) ==
    Some{Game.evaluate(ChessGame.tree(limit, limit, Tables.position(name, key)))} : Maybe<&2, Game.Outcome>}:
  %Equal.sym(Maybe<&2, Cache.Entry>, Registry.find(Tables.generate(capacity, limit), name), Some{Cache.Entry{Directory.width(name), Tables.table(name, limit)}}, directory(capacity, limit, name, bounded)) :
    {Registry.read(Directory.width(name), key, _) == Some{Game.evaluate(ChessGame.tree(limit, limit, Tables.position(name, key)))} : Maybe<&2, Game.Outcome>}
  Equal.trans(Maybe<&2, Game.Outcome>, Cache.lookup(Directory.width(name), key, Cache.Entry{Directory.width(name), Tables.table(name, limit)}),
    Some{Finite.get(Directory.width(name), Game.Outcome, key, Tables.table(name, limit))}, Some{Game.evaluate(ChessGame.tree(limit, limit, Tables.position(name, key)))},
    CacheProof.exact(Directory.width(name), key, Tables.table(name, limit)),
    Equal.cong(Game.Outcome, Maybe<&2, Game.Outcome>, result => Some{result},
      Finite.get(Directory.width(name), Game.Outcome, key, Tables.table(name, limit)), Game.evaluate(ChessGame.tree(limit, limit, Tables.position(name, key))), table(name, limit, key)))

def serialized(+name: List<&2, P.Descriptor>, +limit: Nat, +key: Word(Directory.width(name))) ->
  {Finite.read(Tables.file(name, limit), Finite.offset(Directory.width(name), key)) ==
    Some{Game.byte(Game.evaluate(ChessGame.tree(limit, limit, Tables.position(name, key))))} : Maybe<&2, U32>}:
  +width = Directory.width(name)
  +values = Tables.table(name, limit)
  +actual = Finite.get(width, Game.Outcome, key, values)
  +expected = Game.evaluate(ChessGame.tree(limit, limit, Tables.position(name, key)))
  Equal.trans(Maybe<&2, U32>, Finite.read(Tables.file(name, limit), Finite.offset(width, key)),
    Some{Finite.get(width, U32, key, Engine.bytes(width, values))}, Some{Game.byte(expected)},
    FiniteProof.read_go(width, Engine.bytes(width, values), key, Nil{}),
    Equal.trans(Maybe<&2, U32>, Some{Finite.get(width, U32, key, Engine.bytes(width, values))}, Some{Game.byte(actual)}, Some{Game.byte(expected)},
      Equal.cong(U32, Maybe<&2, U32>, byte => Some{byte}, Finite.get(width, U32, key, Engine.bytes(width, values)), Game.byte(actual), EngineProof.bytes_get(width, values, key)),
      Equal.cong(Game.Outcome, Maybe<&2, U32>, result => Some{Game.byte(result)}, actual, expected, table(name, limit, key))))

def correct(+name: List<&2, P.Descriptor>, +key: Word(Directory.width(name))) ->
  Game.CorrectByte(ChessGame.tree(100n, 100n, Tables.position(name, key)), Finite.read(Tables.file(name, 100n), Finite.offset(Directory.width(name), key))):
  +tree = ChessGame.tree(100n, 100n, Tables.position(name, key))
  (Game.evaluate(tree), (serialized(name, 100n, key), +player =>
    (evidence => GameProof.sound(tree, player, evidence), evidence => GameProof.complete(tree, player, evidence))))

def length(+name: List<&2, P.Descriptor>, +limit: Nat) ->
  {List.length(&2, U32, Tables.file(name, limit)) == Finite.size(Directory.width(name)) : Nat}:
  Equal.trans(Nat, List.length(&2, U32, Tables.file(name, limit)), Nat.add(Finite.size(Directory.width(name)), 0n), Finite.size(Directory.width(name)),
    FiniteProof.length_go(Directory.width(name), Engine.bytes(Directory.width(name), Tables.table(name, limit)), Nil{}), MeasureProof.add_zero(Finite.size(Directory.width(name))))
