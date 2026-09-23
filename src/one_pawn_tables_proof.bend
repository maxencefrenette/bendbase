import Base
import ./game.bend as Game
import ./four_index.bend as Index
import ./four_index_proof.bend as IndexProof
import ./one_pawn_game.bend as Rules
import ./one_pawn_solver.bend as Solver
import ./one_pawn_solver_proof.bend as SolverProof
import ./one_pawn_tables.bend as Tables
import ./finite_table.bend as Finite
import ./finite_table_proof.bend as FiniteProof
import ./pawnless_tables.bend as Bytes
import ./pawnless_tables_proof.bend as ByteProof

def entries_get(depth: Nat, +width: Nat, +limit: Nat, +moves: Nat, +other_moves: Nat, +material: Tables.Profile,
  +keys: Finite.Table(depth, Word(width)), +key: Word(depth)) ->
  {Finite.get(depth, Game.Outcome, key, Tables.entries(depth, width, limit, moves, other_moves, material, keys)) ==
   Tables.value(limit, moves, other_moves, material, Index.decode_at(width, Finite.get(depth, Word(width), key, keys))) : Game.Outcome}:
  match depth keys key:
    case 0n word WNil{}:
      {==}
    case 1n+rest Finite.Fork{left, right} WCon{False{}, tail}:
      entries_get(rest, width, limit, moves, other_moves, material, left, tail)
    case 1n+rest Finite.Fork{left, right} WCon{True{}, tail}:
      entries_get(rest, width, limit, moves, other_moves, material, right, tail)

def lookup(+width: Nat, +limit: Nat, +moves: Nat, +other_moves: Nat, +material: Tables.Profile, +key: Word(width)) ->
  {Finite.get(width, Game.Outcome, key, Tables.generate(width, limit, moves, other_moves, material)) ==
   Tables.value(limit, moves, other_moves, material, Index.decode_at(width, key)) : Game.Outcome}:
  %FiniteProof.keys_get(width, key) :
    {Finite.get(width, Game.Outcome, key, Tables.generate(width, limit, moves, other_moves, material)) ==
     Tables.value(limit, moves, other_moves, material, Index.decode_at(width, _)) : Game.Outcome}
  entries_get(width, width, limit, moves, other_moves, material, Finite.keys(width), key)

def pointwise(+width: Nat, +format: {width == 26n : Nat}, +limit: Nat, +moves: Nat,
  +other_moves: Nat, +material: Tables.Profile, +board: Index.Board) ->
  {Finite.get(width, Game.Outcome, Index.encode_at(width, board), Tables.generate(width, limit, moves, other_moves, material)) ==
   Game.evaluate(Rules.tree(limit, moves, other_moves, Tables.advance(board), Tables.position(material, board))) : Game.Outcome}:
  +key = Index.encode_at(width, board)
  Equal.trans(Game.Outcome,
    Finite.get(width, Game.Outcome, key, Tables.generate(width, limit, moves, other_moves, material)),
    Tables.value(limit, moves, other_moves, material, Index.decode_at(width, key)),
    Game.evaluate(Rules.tree(limit, moves, other_moves, Tables.advance(board), Tables.position(material, board))), lookup(width, limit, moves, other_moves, material, key),
    Equal.trans(Game.Outcome,
      Tables.value(limit, moves, other_moves, material, Index.decode_at(width, key)),
      Tables.value(limit, moves, other_moves, material, board),
      Game.evaluate(Rules.tree(limit, moves, other_moves, Tables.advance(board), Tables.position(material, board))),
      Equal.cong(Index.Board, Game.Outcome, b => Tables.value(limit, moves, other_moves, material, b),
        Index.decode_at(width, key), board, IndexProof.roundtrip_at(width, format, board)),
      SolverProof.pointwise(limit, moves, other_moves, Tables.advance(board), Tables.position(material, board))))

def serialized_value(+width: Nat, +format: {width == 26n : Nat}, +limit: Nat, +moves: Nat,
  +other_moves: Nat, +material: Tables.Profile, +board: Index.Board) ->
  {Finite.read(Tables.file(width, limit, moves, other_moves, material), Finite.offset(width, Index.encode_at(width, board))) ==
   Some{Game.byte(Game.evaluate(Rules.tree(limit, moves, other_moves, Tables.advance(board), Tables.position(material, board))))} : Maybe<&2, U32>}:
  +table = Tables.generate(width, limit, moves, other_moves, material)
  +key = Index.encode_at(width, board)
  +stored = Finite.get(width, U32, key, Bytes.bytes(width, table))
  +value = Finite.get(width, Game.Outcome, key, table)
  +expected = Game.evaluate(Rules.tree(limit, moves, other_moves, Tables.advance(board), Tables.position(material, board)))
  Equal.trans(Maybe<&2, U32>, Finite.read(Tables.file(width, limit, moves, other_moves, material), Finite.offset(width, key)),
    Some{stored}, Some{Game.byte(expected)}, FiniteProof.read_go(width, Bytes.bytes(width, table), key, Nil{}),
    Equal.trans(Maybe<&2, U32>, Some{stored}, Some{Game.byte(value)}, Some{Game.byte(expected)},
      Equal.cong(U32, Maybe<&2, U32>, byte => Some{byte}, stored, Game.byte(value), ByteProof.bytes_get(width, table, key)),
      Equal.cong(Game.Outcome, Maybe<&2, U32>, outcome => Some{Game.byte(outcome)}, value, expected,
        pointwise(width, format, limit, moves, other_moves, material, board))))

def file_length(+width: Nat, +limit: Nat, +moves: Nat, +other_moves: Nat, +material: Tables.Profile) ->
  {List.length(&2, U32, Tables.file(width, limit, moves, other_moves, material)) == Finite.size(width) : Nat}:
  Equal.trans(Nat, List.length(&2, U32, Tables.file(width, limit, moves, other_moves, material)), Nat.add(Finite.size(width), 0n), Finite.size(width),
    FiniteProof.length_go(width, Bytes.bytes(width, Tables.generate(width, limit, moves, other_moves, material)), Nil{}),
    ByteProof.add_zero(Finite.size(width)))
