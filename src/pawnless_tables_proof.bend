import Base
import ./game.bend as Game
import ./pawnless_chess.bend as Chess
import ./pawnless_index.bend as Index
import ./pawnless_index_proof.bend as IndexProof
import ./finite_table.bend as Finite
import ./finite_table_proof.bend as FiniteProof
import ./pawnless_tables.bend as Tables

def initial_get(depth: Nat, +width: Nat, +material: Chess.Material,
  +keys: Finite.Table(depth, Word(width)), +key: Word(depth)) ->
  {Finite.get(depth, Game.Outcome, key, Tables.initial(depth, width, material, keys)) ==
   Tables.base(width, material, Finite.get(depth, Word(width), key, keys)) : Game.Outcome}:
  match depth keys key:
    case 0n word WNil{}:
      {==}
    case 1n+rest Finite.Fork{left, right} WCon{False{}, tail}:
      initial_get(rest, width, material, left, tail)
    case 1n+rest Finite.Fork{left, right} WCon{True{}, tail}:
      initial_get(rest, width, material, right, tail)

def layer_get(depth: Nat, +width: Nat, +material: Chess.Material,
  +previous: Finite.Table(width, Game.Outcome),
  +keys: Finite.Table(depth, Word(width)), +key: Word(depth)) ->
  {Finite.get(depth, Game.Outcome, key, Tables.layer(depth, width, material, previous, keys)) ==
   Tables.step(width, material, previous, Finite.get(depth, Word(width), key, keys)) : Game.Outcome}:
  match depth keys key:
    case 0n word WNil{}:
      {==}
    case 1n+rest Finite.Fork{left, right} WCon{False{}, tail}:
      layer_get(rest, width, material, previous, left, tail)
    case 1n+rest Finite.Fork{left, right} WCon{True{}, tail}:
      layer_get(rest, width, material, previous, right, tail)

def initial_lookup(+width: Nat, +material: Chess.Material, +keys: Finite.Table(width, Word(width)), +key: Word(width),
  canonical: {Finite.get(width, Word(width), key, keys) == key : Word(width)}) ->
  {Finite.get(width, Game.Outcome, key, Tables.initial(width, width, material, keys)) == Tables.base(width, material, key) : Game.Outcome}:
  %canonical : {Finite.get(width, Game.Outcome, key, Tables.initial(width, width, material, keys)) == Tables.base(width, material, _) : Game.Outcome}
  initial_get(width, width, material, keys, key)

def layer_lookup(+width: Nat, +material: Chess.Material, +previous: Finite.Table(width, Game.Outcome),
  +keys: Finite.Table(width, Word(width)), +key: Word(width),
  canonical: {Finite.get(width, Word(width), key, keys) == key : Word(width)}) ->
  {Finite.get(width, Game.Outcome, key, Tables.layer(width, width, material, previous, keys)) == Tables.step(width, material, previous, key) : Game.Outcome}:
  %canonical : {Finite.get(width, Game.Outcome, key, Tables.layer(width, width, material, previous, keys)) == Tables.step(width, material, previous, _) : Game.Outcome}
  layer_get(width, width, material, previous, keys, key)

def lookup_base(+width: Nat, +size: {width == 20n : Nat}, +material: Chess.Material, +board: Chess.Board) ->
  {Finite.get(width, Game.Outcome, Index.encode_at(width, board), Tables.generate(0n, width, material)) ==
   Game.evaluate(Chess.boundary(Chess.view(material, Chess.Three{board}))) : Game.Outcome}:
  %IndexProof.roundtrip_at(width, size, board) :
    {Finite.get(width, Game.Outcome, Index.encode_at(width, board), Tables.generate(0n, width, material)) ==
     Game.evaluate(Chess.boundary(Chess.view(material, Chess.Three{_}))) : Game.Outcome}
  initial_lookup(width, material, Finite.keys(width), Index.encode_at(width, board), FiniteProof.keys_get(width, Index.encode_at(width, board)))

def lookup_step(+remaining: Nat, +width: Nat, +size: {width == 20n : Nat}, +material: Chess.Material, +board: Chess.Board) ->
  {Finite.get(width, Game.Outcome, Index.encode_at(width, board), Tables.generate(1n+remaining, width, material)) ==
   Tables.combine(Chess.view(material, Chess.Three{board}),
     Tables.values(Chess.children(Chess.view(material, Chess.Three{board})), width, Tables.generate(remaining, width, material))) : Game.Outcome}:
  %IndexProof.roundtrip_at(width, size, board) :
    {Finite.get(width, Game.Outcome, Index.encode_at(width, board), Tables.generate(1n+remaining, width, material)) ==
     Tables.at(width, material, Tables.generate(remaining, width, material), _) : Game.Outcome}
  layer_lookup(width, material, Tables.generate(remaining, width, material), Finite.keys(width), Index.encode_at(width, board), FiniteProof.keys_get(width, Index.encode_at(width, board)))

def outcomes(trees: List<&2, Game.Tree>) -> List<&2, Game.Outcome>:
  match trees:
    case Nil{}:
      Nil{}
    case head <> tail:
      Game.evaluate(head) <> outcomes(tail)

def choices_evaluate(rest: List<&2, Game.Tree>, +turn: Game.Player, +first: Game.Tree) ->
  {Game.evaluate(Chess.choices(rest, turn, first)) ==
   Tables.fold(outcomes(rest), turn, Game.evaluate(first)) : Game.Outcome}:
  match rest:
    case Nil{}:
      {==}
    case +head <> +tail:
      Equal.cong(Game.Outcome, Game.Outcome, value => Game.best(turn, Game.evaluate(first), value),
        Game.evaluate(Chess.choices(tail, turn, head)),
        Tables.fold(outcomes(tail), turn, Game.evaluate(head)), choices_evaluate(tail, turn, head))

def assemble_evaluate(+view: Chess.View, +trees: List<&2, Game.Tree>) ->
  {Tables.combine(view, outcomes(trees)) == Game.evaluate(Chess.assemble(view, trees)) : Game.Outcome}:
  match view trees:
    case Chess.Stop{outcome} _:
      {==}
    case Chess.Play{turn, children} Nil{}:
      {==}
    case Chess.Play{+turn, children} +head <> +tail:
      Equal.sym(Game.Outcome, Game.evaluate(Chess.choices(tail, turn, head)),
        Tables.fold(outcomes(tail), turn, Game.evaluate(head)), choices_evaluate(tail, turn, head))

def cons_cong(-A: Data, +x: A, +y: A, +xs: List<&2, A>, +ys: List<&2, A>,
  head: {x == y : A}, tail: {xs == ys : List<&2, A>}) ->
  {x <> xs == y <> ys : List<&2, A>}:
  %head : {x <> xs == _ <> ys : List<&2, A>}
  %tail : {x <> xs == x <> _ : List<&2, A>}
  {==}

def step_from_children(+remaining: Nat, +width: Nat, +size: {width == 20n : Nat}, +material: Chess.Material, +board: Chess.Board,
  children_correct:
    {Tables.values(Chess.children(Chess.view(material, Chess.Three{board})), width, Tables.generate(remaining, width, material)) ==
     outcomes(Chess.forest(remaining, material, Chess.children(Chess.view(material, Chess.Three{board})))) : List<&2, Game.Outcome>}) ->
  {Finite.get(width, Game.Outcome, Index.encode_at(width, board), Tables.generate(1n+remaining, width, material)) ==
   Game.evaluate(Chess.assemble(Chess.view(material, Chess.Three{board}),
     Chess.forest(remaining, material, Chess.children(Chess.view(material, Chess.Three{board}))))) : Game.Outcome}:
  +node = Chess.view(material, Chess.Three{board})
  +prior = Tables.values(Chess.children(node), width, Tables.generate(remaining, width, material))
  +trees = Chess.forest(remaining, material, Chess.children(node))
  Equal.trans(Game.Outcome,
    Finite.get(width, Game.Outcome, Index.encode_at(width, board), Tables.generate(1n+remaining, width, material)),
    Tables.combine(node, prior), Game.evaluate(Chess.assemble(node, trees)),
    lookup_step(remaining, width, size, material, board),
    Equal.trans(Game.Outcome, Tables.combine(node, prior),
      Tables.combine(node, outcomes(trees)), Game.evaluate(Chess.assemble(node, trees)),
      Equal.cong(List<&2, Game.Outcome>, Game.Outcome, values => Tables.combine(node, values),
        prior, outcomes(trees), children_correct), assemble_evaluate(node, trees)))

# One induction over the clock and an arbitrary list of positions. The list
# stays symbolic: this never evaluates any of the concrete table entries.
def forest_correct(remaining: Nat, +states: List<&2, Chess.State>, +width: Nat, +size: {width == 20n : Nat}, +material: Chess.Material) ->
  {Tables.values(states, width, Tables.generate(remaining, width, material)) ==
   outcomes(Chess.forest(remaining, material, states)) : List<&2, Game.Outcome>}:
  match remaining states:
    case 0n Nil{}:
      {==}
    case 1n+rest Nil{}:
      {==}
    case 0n Chess.KingsOnly{} <> +tail:
      cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        Tables.values(tail, width, Tables.generate(0n, width, material)), outcomes(Chess.forest(0n, material, tail)),
        {==}, forest_correct(0n, tail, width, size, material))
    case 0n Chess.Three{+board} <> +tail:
      cons_cong(Game.Outcome,
        Finite.get(width, Game.Outcome, Index.encode_at(width, board), Tables.generate(0n, width, material)),
        Game.evaluate(Chess.boundary(Chess.view(material, Chess.Three{board}))),
        Tables.values(tail, width, Tables.generate(0n, width, material)), outcomes(Chess.forest(0n, material, tail)),
        lookup_base(width, size, material, board), forest_correct(0n, tail, width, size, material))
    case 1n++rest Chess.KingsOnly{} <> +tail:
      cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        Tables.values(tail, width, Tables.generate(1n+rest, width, material)), outcomes(Chess.forest(1n+rest, material, tail)),
        {==}, forest_correct(1n+rest, tail, width, size, material))
    case 1n++rest Chess.Three{+board} <> +tail:
      +node = Chess.view(material, Chess.Three{board})
      cons_cong(Game.Outcome,
        Finite.get(width, Game.Outcome, Index.encode_at(width, board), Tables.generate(1n+rest, width, material)),
        Game.evaluate(Chess.assemble(node, Chess.forest(rest, material, Chess.children(node)))),
        Tables.values(tail, width, Tables.generate(1n+rest, width, material)), outcomes(Chess.forest(1n+rest, material, tail)),
        step_from_children(rest, width, size, material, board, forest_correct(rest, Chess.children(node), width, size, material)),
        forest_correct(1n+rest, tail, width, size, material))

def first(outcomes: List<&2, Game.Outcome>) -> Game.Outcome:
  match outcomes:
    case Nil{}:
      Game.Draw{}
    case head <> tail:
      head

def first_outcomes(+trees: List<&2, Game.Tree>) ->
  {first(outcomes(trees)) == Game.evaluate(Chess.only(trees)) : Game.Outcome}:
  match trees:
    case Nil{}:
      {==}
    case head <> tail:
      {==}

def pointwise(+remaining: Nat, +width: Nat, +size: {width == 20n : Nat}, +material: Chess.Material, +board: Chess.Board) ->
  {Finite.get(width, Game.Outcome, Index.encode_at(width, board), Tables.generate(remaining, width, material)) ==
   Game.evaluate(Chess.tree(remaining, material, board)) : Game.Outcome}:
  +states = {Chess.Three{board} <> Nil{} : List<&2, Chess.State>}
  +trees = Chess.forest(remaining, material, states)
  Equal.trans(Game.Outcome,
    Finite.get(width, Game.Outcome, Index.encode_at(width, board), Tables.generate(remaining, width, material)),
    first(outcomes(trees)), Game.evaluate(Chess.tree(remaining, material, board)),
    Equal.cong(List<&2, Game.Outcome>, Game.Outcome, values => first(values),
      Tables.values(states, width, Tables.generate(remaining, width, material)), outcomes(trees),
      forest_correct(remaining, states, width, size, material)), first_outcomes(trees))

def bytes_get(depth: Nat, +table: Finite.Table(depth, Game.Outcome), +key: Word(depth)) ->
  {Finite.get(depth, U32, key, Tables.bytes(depth, table)) ==
   Game.byte(Finite.get(depth, Game.Outcome, key, table)) : U32}:
  match depth table key:
    case 0n outcome WNil{}:
      {==}
    case 1n+rest Finite.Fork{left, right} WCon{False{}, tail}:
      bytes_get(rest, left, tail)
    case 1n+rest Finite.Fork{left, right} WCon{True{}, tail}:
      bytes_get(rest, right, tail)

def serialized_value(+remaining: Nat, +width: Nat, +size: {width == 20n : Nat},
  +material: Chess.Material, +board: Chess.Board) ->
  {Finite.read(Tables.file(remaining, width, material), Finite.offset(width, Index.encode_at(width, board))) ==
   Some{Game.byte(Game.evaluate(Chess.tree(remaining, material, board)))} : Maybe<&2, U32>}:
  +table = Tables.generate(remaining, width, material)
  +key = Index.encode_at(width, board)
  +stored = Finite.get(width, U32, key, Tables.bytes(width, table))
  +value = Finite.get(width, Game.Outcome, key, table)
  +expected = Game.evaluate(Chess.tree(remaining, material, board))
  Equal.trans(Maybe<&2, U32>,
    Finite.read(Tables.file(remaining, width, material), Finite.offset(width, key)),
    Some{stored}, Some{Game.byte(expected)},
    FiniteProof.read_go(width, Tables.bytes(width, table), key, Nil{}),
    Equal.trans(Maybe<&2, U32>, Some{stored}, Some{Game.byte(value)}, Some{Game.byte(expected)},
      Equal.cong(U32, Maybe<&2, U32>, byte => Some{byte}, stored, Game.byte(value), bytes_get(width, table, key)),
      Equal.cong(Game.Outcome, Maybe<&2, U32>, outcome => Some{Game.byte(outcome)}, value, expected,
        pointwise(remaining, width, size, material, board))))

def add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def file_length(+remaining: Nat, +width: Nat, +material: Chess.Material) ->
  {List.length(&2, U32, Tables.file(remaining, width, material)) == Finite.size(width) : Nat}:
  Equal.trans(Nat, List.length(&2, U32, Tables.file(remaining, width, material)),
    Nat.add(Finite.size(width), 0n), Finite.size(width),
    FiniteProof.length_go(width, Tables.bytes(width, Tables.generate(remaining, width, material)), Nil{}),
    add_zero(Finite.size(width)))
