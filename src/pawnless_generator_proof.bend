import Base
import ./game.bend as Game
import ./pawnless_chess.bend as Three
import ./pawnless_index.bend as Index
import ./pawnless_index_proof.bend as IndexProof
import ./four_index.bend as FourIndex
import ./four_index_proof.bend as FourIndexProof
import ./material_chess.bend as Chess
import ./four_chess.bend as Rules
import ./pawnless_generator.bend as Gen
import ./clock_solver.bend as Solver
import ./clock_solver_proof.bend as SolverProof
import ./pawnless_cache_shape.bend as Shape
import ./finite_table.bend as Finite
import ./finite_table_proof.bend as FiniteProof
import ./pawnless_tables.bend as Bytes
import ./pawnless_tables_proof.bend as Lemmas

def assemble_evaluate(+node: Rules.View, +trees: List<&2, Game.Tree>) ->
  {Gen.combine(node, Lemmas.outcomes(trees)) == Game.evaluate(Rules.assemble(node, trees)) : Game.Outcome}:
  match node trees:
    case Rules.Stop{result} _:
      {==}
    case Rules.Play{turn, children} Nil{}:
      {==}
    case Rules.Play{+turn, children} +head <> +tail:
      Equal.sym(Game.Outcome, Game.evaluate(Three.choices(tail, turn, head)),
        Bytes.fold(Lemmas.outcomes(tail), turn, Game.evaluate(head)),
        Lemmas.choices_evaluate(tail, turn, head))

def combine_correct(+node: Rules.View, +values: List<&2, Game.Outcome>, +trees: List<&2, Game.Tree>,
  correct: {values == Lemmas.outcomes(trees) : List<&2, Game.Outcome>}) ->
  {Gen.combine(node, values) == Game.evaluate(Rules.assemble(node, trees)) : Game.Outcome}:
  Equal.trans(Game.Outcome, Gen.combine(node, values), Gen.combine(node, Lemmas.outcomes(trees)),
    Game.evaluate(Rules.assemble(node, trees)),
    Equal.cong(List<&2, Game.Outcome>, Game.Outcome, xs => Gen.combine(node, xs),
      values, Lemmas.outcomes(trees), correct), assemble_evaluate(node, trees))

def graph_get(depth: Nat, +width: Nat, +low: Nat, +scope: Gen.Scope,
  +moves: Nat, +lower: Maybe<&2, Gen.Bundle<low>>, +keys: Finite.Table(depth, Word(width)), +key: Word(depth)) ->
  {Finite.get(depth, Solver.Node<width>, key, Gen.graph_fill(depth, width, low, scope, moves, lower, keys)) ==
   Gen.node(width, low, scope, lower, Rules.view(moves, Gen.decode(width, scope, Finite.get(depth, Word(width), key, keys)))) : Solver.Node<width>}:
  match depth keys key:
    case 0n word WNil{}:
      {==}
    case 1n+rest Finite.Fork{left, right} WCon{False{}, tail}:
      graph_get(rest, width, low, scope, moves, lower, left, tail)
    case 1n+rest Finite.Fork{left, right} WCon{True{}, tail}:
      graph_get(rest, width, low, scope, moves, lower, right, tail)

def graph_lookup(+width: Nat, +low: Nat, +scope: Gen.Scope,
  +moves: Nat, +lower: Maybe<&2, Gen.Bundle<low>>, +key: Word(width)) ->
  {Finite.get(width, Solver.Node<width>, key, Gen.graph(width, low, scope, moves, lower)) ==
   Gen.node(width, low, scope, lower, Rules.view(moves, Gen.decode(width, scope, key))) : Solver.Node<width>}:
  %FiniteProof.keys_get(width, key) :
    {Finite.get(width, Solver.Node<width>, key, Gen.graph(width, low, scope, moves, lower)) ==
     Gen.node(width, low, scope, lower, Rules.view(moves, Gen.decode(width, scope, _))) : Solver.Node<width>}
  graph_get(width, width, low, scope, moves, lower, Finite.keys(width), key)

def edge_values(positions: List<&2, Chess.Position>, +width: Nat, +low: Nat, +scope: Gen.Scope,
  +previous: Finite.Table(width, Game.Outcome), +lower: Maybe<&2, Gen.Bundle<low>>) ->
  {Solver.values(width, Gen.edges(positions, width, low, scope, lower), previous) ==
   Gen.values(positions, width, low, scope, previous, lower) : List<&2, Game.Outcome>}:
  match positions:
    case Nil{}:
      {==}
    case head <> +tail:
      +value = Gen.lookup(width, low, scope, previous, lower, head)
      Equal.cong(List<&2, Game.Outcome>, List<&2, Game.Outcome>, rest => value <> rest,
        Solver.values(width, Gen.edges(tail, width, low, scope, lower), previous),
        Gen.values(tail, width, low, scope, previous, lower),
        edge_values(tail, width, low, scope, previous, lower))

def compiled_combine(+width: Nat, +low: Nat, +scope: Gen.Scope, +lower: Maybe<&2, Gen.Bundle<low>>,
  +view: Rules.View, +values: List<&2, Game.Outcome>) ->
  {Solver.combine(width, Gen.node(width, low, scope, lower, view), values) == Gen.combine(view, values) : Game.Outcome}:
  match view values:
    case Rules.Stop{result} _:
      {==}
    case Rules.Play{turn, children} Nil{}:
      {==}
    case Rules.Play{turn, children} head <> tail:
      {==}

def compiled_boundary(+width: Nat, +low: Nat, +scope: Gen.Scope, +lower: Maybe<&2, Gen.Bundle<low>>, +view: Rules.View) ->
  {Solver.boundary(width, Gen.node(width, low, scope, lower, view)) == Game.evaluate(Rules.boundary(view)) : Game.Outcome}:
  match view:
    case Rules.Stop{result}:
      {==}
    case Rules.Play{turn, children}:
      {==}

def compiled_step(+width: Nat, +low: Nat, +scope: Gen.Scope, +previous: Finite.Table(width, Game.Outcome),
  +lower: Maybe<&2, Gen.Bundle<low>>, +view: Rules.View) ->
  {Solver.at(width, Solver.Next{previous}, Gen.node(width, low, scope, lower, view)) ==
   Gen.combine(view, Gen.values(Rules.children(view), width, low, scope, previous, lower)) : Game.Outcome}:
  match view:
    case Rules.Stop{result}:
      {==}
    case Rules.Play{turn, +children}:
      Equal.trans(Game.Outcome,
        Solver.at(width, Solver.Next{previous}, Gen.node(width, low, scope, lower, view)),
        Solver.combine(width, Gen.node(width, low, scope, lower, view), Gen.values(children, width, low, scope, previous, lower)),
        Gen.combine(view, Gen.values(children, width, low, scope, previous, lower)),
        Equal.cong(List<&2, Game.Outcome>, Game.Outcome, values => Solver.combine(width, Gen.node(width, low, scope, lower, view), values),
          Solver.values(width, Gen.edges(children, width, low, scope, lower), previous), Gen.values(children, width, low, scope, previous, lower),
          edge_values(children, width, low, scope, previous, lower)),
        compiled_combine(width, low, scope, lower, view, Gen.values(children, width, low, scope, previous, lower)))

def compiled_at(+width: Nat, +low: Nat, +scope: Gen.Scope, +phase: Solver.Layer<width>,
  +lower: Maybe<&2, Gen.Bundle<low>>, +moves: Nat, +position: Chess.Position) ->
  {Solver.at(width, phase, Gen.node(width, low, scope, lower, Rules.view(moves, position))) ==
   Gen.at(width, low, scope, phase, lower, moves, position) : Game.Outcome}:
  match phase:
    case Solver.Initial{}:
      compiled_boundary(width, low, scope, lower, Rules.view(moves, position))
    case Solver.Next{previous}:
      compiled_step(width, low, scope, previous, lower, Rules.view(moves, position))

def layer_at(+width: Nat, +low: Nat, +scope: Gen.Scope, +phase: Solver.Layer<width>,
  +lower: Maybe<&2, Gen.Bundle<low>>, +moves: Nat, +key: Word(width)) ->
  {Finite.get(width, Game.Outcome, key, Solver.layer(width, Gen.graph(width, low, scope, moves, lower), phase)) ==
   Gen.at(width, low, scope, phase, lower, moves, Gen.decode(width, scope, key)) : Game.Outcome}:
  +graph = Gen.graph(width, low, scope, moves, lower)
  +position = Gen.decode(width, scope, key)
  +node = Gen.node(width, low, scope, lower, Rules.view(moves, position))
  Equal.trans(Game.Outcome,
    Finite.get(width, Game.Outcome, key, Solver.layer(width, graph, phase)),
    Solver.at(width, phase, node), Gen.at(width, low, scope, phase, lower, moves, position),
    Equal.trans(Game.Outcome,
      Finite.get(width, Game.Outcome, key, Solver.layer(width, graph, phase)),
      Solver.at(width, phase, Finite.get(width, Solver.Node<width>, key, graph)), Solver.at(width, phase, node),
      SolverProof.lookup(width, graph, phase, key),
      Equal.cong(Solver.Node<width>, Game.Outcome, n => Solver.at(width, phase, n),
        Finite.get(width, Solver.Node<width>, key, graph), node, graph_lookup(width, low, scope, moves, lower, key))),
    compiled_at(width, low, scope, phase, lower, moves, position))

def generated_get(+remaining: Nat, +width: Nat, +low: Nat, +scope: Gen.Scope,
  +moves: Nat, +lower: Maybe<&2, Gen.Bundle<low>>, +key: Word(width)) ->
  {Finite.get(width, Game.Outcome, key, Gen.generate(remaining, width, low, scope, moves, lower)) ==
   Gen.at(width, low, scope, Gen.phase(remaining, width, low, scope, moves, lower), lower, moves, Gen.decode(width, scope, key)) : Game.Outcome}:
  match remaining:
    case 0n:
      layer_at(width, low, scope, Solver.Initial{}, lower, moves, key)
    case 1n+rest:
      layer_at(width, low, scope, Solver.Next{Gen.generate(rest, width, low, scope, moves, lower)}, lower, moves, key)

def generated_at(+remaining: Nat, +width: Nat, +low: Nat, +scope: Gen.Scope,
  +moves: Nat, +lower: Maybe<&2, Gen.Bundle<low>>, +key: Word(width), +position: Chess.Position,
  decoded: {Gen.decode(width, scope, key) == position : Chess.Position}) ->
  {Finite.get(width, Game.Outcome, key, Gen.generate(remaining, width, low, scope, moves, lower)) ==
   Gen.at(width, low, scope, Gen.phase(remaining, width, low, scope, moves, lower), lower, moves, position) : Game.Outcome}:
  %decoded :
    {Finite.get(width, Game.Outcome, key, Gen.generate(remaining, width, low, scope, moves, lower)) ==
     Gen.at(width, low, scope, Gen.phase(remaining, width, low, scope, moves, lower), lower, moves, _) : Game.Outcome}
  generated_get(remaining, width, low, scope, moves, lower, key)

def single_decode(+width: Nat, size: {width == 20n : Nat}, +kind: Three.Material, +actual: Three.Material,
  +board: Three.Board, same: {actual == kind : Three.Material}) ->
  {Gen.decode(width, Gen.Single{kind}, Index.encode_at(width, board)) == Chess.from_three(actual, board) : Chess.Position}:
  Equal.trans(Chess.Position, Gen.decode(width, Gen.Single{kind}, Index.encode_at(width, board)),
    Chess.from_three(kind, board), Chess.from_three(actual, board),
    Equal.cong(Three.Board, Chess.Position, b => Chess.from_three(kind, b),
      Index.decode_at(width, Index.encode_at(width, board)), board, IndexProof.roundtrip_at(width, size, board)),
    Equal.cong(Three.Material, Chess.Position, k => Chess.from_three(k, board), kind, actual,
      Equal.sym(Three.Material, actual, kind, same)))

def single_at(+remaining: Nat, +width: Nat, +size: {width == 20n : Nat}, +moves: Nat,
  +kind: Three.Material, +actual: Three.Material, +board: Three.Board, same: {actual == kind : Three.Material}) ->
  {Finite.get(width, Game.Outcome, Index.encode_at(width, board), Gen.generate(remaining, width, width, Gen.Single{kind}, moves, None{})) ==
   Gen.at(width, width, Gen.Single{kind}, Gen.phase(remaining, width, width, Gen.Single{kind}, moves, None{}),
     None{}, moves, Chess.from_three(actual, board)) : Game.Outcome}:
  generated_at(remaining, width, width, Gen.Single{kind}, moves, None{}, Index.encode_at(width, board),
    Chess.from_three(actual, board), single_decode(width, size, kind, actual, board, same))

def single_step(+remaining: Nat, +width: Nat, +size: {width == 20n : Nat}, +moves: Nat,
  +kind: Three.Material, +actual: Three.Material, +board: Three.Board, same: {actual == kind : Three.Material},
  children:
    {Gen.values(Rules.children(Rules.view(moves, Chess.from_three(actual, board))), width, width, Gen.Single{kind},
       Gen.generate(remaining, width, width, Gen.Single{kind}, moves, None{}), None{}) ==
     Lemmas.outcomes(Rules.single(remaining, Rules.children(Rules.view(moves, Chess.from_three(actual, board))), moves)) : List<&2, Game.Outcome>}) ->
  {Finite.get(width, Game.Outcome, Index.encode_at(width, board), Gen.generate(1n+remaining, width, width, Gen.Single{kind}, moves, None{})) ==
   Game.evaluate(Rules.assemble(Rules.view(moves, Chess.from_three(actual, board)),
     Rules.single(remaining, Rules.children(Rules.view(moves, Chess.from_three(actual, board))), moves))) : Game.Outcome}:
  +node = Rules.view(moves, Chess.from_three(actual, board))
  +values = Gen.values(Rules.children(node), width, width, Gen.Single{kind},
    Gen.generate(remaining, width, width, Gen.Single{kind}, moves, None{}), None{})
  +trees = Rules.single(remaining, Rules.children(node), moves)
  Equal.trans(Game.Outcome,
    Finite.get(width, Game.Outcome, Index.encode_at(width, board), Gen.generate(1n+remaining, width, width, Gen.Single{kind}, moves, None{})),
    Gen.combine(node, values), Game.evaluate(Rules.assemble(node, trees)),
    single_at(1n+remaining, width, size, moves, kind, actual, board, same),
    combine_correct(node, values, trees, children))

def and_false(+value: Bool) -> {value && False{} == False{} : Bool}:
  match value:
    case False{}:
      {==}
    case True{}:
      {==}

def bare_view(+moves: Nat, +turn: Game.Player, +wk: Word(6n), +bk: Word(6n)) ->
  {Rules.view(moves, Chess.Position{turn, wk, bk, Nil{}}) == Rules.Stop{Game.Draw{}} : Rules.View}:
  +position = {Chess.Position{turn, wk, bk, Nil{}} : Chess.Position}
  Equal.cong(Bool, Rules.View, live => Rules.view.live(live, moves, position),
    Chess.valid(position) && False{}, False{}, and_false(Chess.valid(position)))

def bare_single(remaining: Nat, +moves: Nat, +turn: Game.Player, +wk: Word(6n), +bk: Word(6n)) ->
  {Game.Draw{} == Game.evaluate(Three.only(Rules.single(remaining, Chess.Position{turn, wk, bk, Nil{}} <> Nil{}, moves))) : Game.Outcome}:
  match remaining:
    case 0n:
      Equal.cong(Rules.View, Game.Outcome, node => Game.evaluate(Rules.boundary(node)),
        Rules.Stop{Game.Draw{}}, Rules.view(moves, Chess.Position{turn, wk, bk, Nil{}}),
        Equal.sym(Rules.View, Rules.view(moves, Chess.Position{turn, wk, bk, Nil{}}), Rules.Stop{Game.Draw{}}, bare_view(moves, turn, wk, bk)))
    case 1n++clock:
      Equal.cong(Rules.View, Game.Outcome, node => Game.evaluate(Rules.assemble(node, Rules.single(clock, Rules.children(node), moves))),
        Rules.Stop{Game.Draw{}}, Rules.view(moves, Chess.Position{turn, wk, bk, Nil{}}),
        Equal.sym(Rules.View, Rules.view(moves, Chess.Position{turn, wk, bk, Nil{}}), Rules.Stop{Game.Draw{}}, bare_view(moves, turn, wk, bk)))

# Induction over the clock and a symbolic list, never over all board positions.
def single_forest(remaining: Nat, +positions: List<&2, Chess.Position>, +width: Nat,
  +size: {width == 20n : Nat}, +moves: Nat, +kind: Three.Material,
  all: Shape.All(Gen.Single{kind}, positions)) ->
  {Gen.values(positions, width, width, Gen.Single{kind}, Gen.generate(remaining, width, width, Gen.Single{kind}, moves, None{}), None{}) ==
   Lemmas.outcomes(Rules.single(remaining, positions, moves)) : List<&2, Game.Outcome>}:
  match remaining positions all:
    case 0n Nil{} _:
      {==}
    case 0n Chess.Position{+turn, +wk, +bk, Nil{}} <> +tail Shape.Both{head, rest}:
      Lemmas.cons_cong(Game.Outcome, Game.Draw{},
        Game.evaluate(Three.only(Rules.single(0n, Chess.Position{turn, wk, bk, Nil{}} <> Nil{}, moves))),
        Gen.values(tail, width, width, Gen.Single{kind}, Gen.generate(0n, width, width, Gen.Single{kind}, moves, None{}), None{}),
        Lemmas.outcomes(Rules.single(0n, tail, moves)), bare_single(0n, moves, turn, wk, bk),
        single_forest(0n, tail, width, size, moves, kind, rest))
    case 0n Chess.Position{+turn, +wk, +bk, Chess.Man{+owner, +actual, +pc} <> Nil{}} <> +tail Shape.Both{+same, rest}:
      +board = {Three.Board{owner, turn, wk, bk, pc} : Three.Board}
      +position = Chess.from_three(actual, board)
      Lemmas.cons_cong(Game.Outcome,
        Finite.get(width, Game.Outcome, Index.encode_at(width, board), Gen.generate(0n, width, width, Gen.Single{kind}, moves, None{})),
        Game.evaluate(Three.only(Rules.single(0n, position <> Nil{}, moves))),
        Gen.values(tail, width, width, Gen.Single{kind}, Gen.generate(0n, width, width, Gen.Single{kind}, moves, None{}), None{}),
        Lemmas.outcomes(Rules.single(0n, tail, moves)),
        single_at(0n, width, size, moves, kind, actual, board, same),
        single_forest(0n, tail, width, size, moves, kind, rest))
    case 0n Chess.Position{turn, wk, bk, Chess.Man{owner, actual, pc} <> man <> men} <> tail Shape.Both{bad, rest}:
      match bad:
    case 1n++clock Nil{} _:
      {==}
    case 1n++clock Chess.Position{+turn, +wk, +bk, Nil{}} <> +tail Shape.Both{head, rest}:
      Lemmas.cons_cong(Game.Outcome, Game.Draw{},
        Game.evaluate(Three.only(Rules.single(1n+clock, Chess.Position{turn, wk, bk, Nil{}} <> Nil{}, moves))),
        Gen.values(tail, width, width, Gen.Single{kind}, Gen.generate(1n+clock, width, width, Gen.Single{kind}, moves, None{}), None{}),
        Lemmas.outcomes(Rules.single(1n+clock, tail, moves)), bare_single(1n+clock, moves, turn, wk, bk),
        single_forest(1n+clock, tail, width, size, moves, kind, rest))
    case 1n++clock Chess.Position{+turn, +wk, +bk, Chess.Man{+owner, +actual, +pc} <> Nil{}} <> +tail Shape.Both{+same, rest}:
      +board = {Three.Board{owner, turn, wk, bk, pc} : Three.Board}
      +position = Chess.from_three(actual, board)
      Lemmas.cons_cong(Game.Outcome,
        Finite.get(width, Game.Outcome, Index.encode_at(width, board), Gen.generate(1n+clock, width, width, Gen.Single{kind}, moves, None{})),
        Game.evaluate(Three.only(Rules.single(1n+clock, position <> Nil{}, moves))),
        Gen.values(tail, width, width, Gen.Single{kind}, Gen.generate(1n+clock, width, width, Gen.Single{kind}, moves, None{}), None{}),
        Lemmas.outcomes(Rules.single(1n+clock, tail, moves)),
        single_step(clock, width, size, moves, kind, actual, board, same,
          single_forest(clock, Rules.children(Rules.view(moves, position)), width, size, moves, kind,
            Shape.children(moves, Gen.Single{kind}, position, same))),
        single_forest(1n+clock, tail, width, size, moves, kind, rest))
    case 1n++clock Chess.Position{turn, wk, bk, Chess.Man{owner, actual, pc} <> man <> men} <> tail Shape.Both{bad, rest}:
      match bad:

def only_correct(+values: List<&2, Game.Outcome>, +trees: List<&2, Game.Tree>,
  correct: {values == Lemmas.outcomes(trees) : List<&2, Game.Outcome>}) ->
  {Lemmas.first(values) == Game.evaluate(Three.only(trees)) : Game.Outcome}:
  Equal.trans(Game.Outcome, Lemmas.first(values), Lemmas.first(Lemmas.outcomes(trees)),
    Game.evaluate(Three.only(trees)),
    Equal.cong(List<&2, Game.Outcome>, Game.Outcome, xs => Lemmas.first(xs), values, Lemmas.outcomes(trees), correct),
    Lemmas.first_outcomes(trees))

def single_pointwise(+remaining: Nat, +width: Nat, +size: {width == 20n : Nat}, +moves: Nat,
  +kind: Three.Material, +board: Three.Board) ->
  {Finite.get(width, Game.Outcome, Index.encode_at(width, board), Gen.generate(remaining, width, width, Gen.Single{kind}, moves, None{})) ==
   Game.evaluate(Three.only(Rules.single(remaining, Chess.from_three(kind, board) <> Nil{}, moves))) : Game.Outcome}:
  match board:
    case Three.Board{owner, turn, wk, bk, pc}:
      +positions = {Chess.from_three(kind, board) <> Nil{} : List<&2, Chess.Position>}
      only_correct(
        Gen.values(positions, width, width, Gen.Single{kind}, Gen.generate(remaining, width, width, Gen.Single{kind}, moves, None{}), None{}),
        Rules.single(remaining, positions, moves),
        single_forest(remaining, positions, width, size, moves, kind, Shape.Both{{==}, Unit{}}))

def selected(+remaining: Nat, +width: Nat, +moves: Nat, +kind: Three.Material) ->
  {Gen.select(width, kind, Gen.singles(remaining, width, moves)) ==
   Gen.generate(remaining, width, width, Gen.Single{kind}, moves, None{}) : Finite.Table(width, Game.Outcome)}:
  match kind:
    case Three.Queen{}:
      {==}
    case Three.Rook{}:
      {==}
    case Three.Bishop{}:
      {==}
    case Three.Knight{}:
      {==}

def lower_correct(+limit: Nat, +width: Nat, +size: {width == 20n : Nat}, +moves: Nat,
  +kind: Three.Material, +board: Three.Board) ->
  {Gen.lower_value(width, Some{Gen.singles(limit, width, moves)}, kind, board) ==
   Game.evaluate(Three.only(Rules.single(limit, Chess.from_three(kind, board) <> Nil{}, moves))) : Game.Outcome}:
  Equal.trans(Game.Outcome, Gen.lower_value(width, Some{Gen.singles(limit, width, moves)}, kind, board),
    Finite.get(width, Game.Outcome, Index.encode_at(width, board), Gen.generate(limit, width, width, Gen.Single{kind}, moves, None{})),
    Game.evaluate(Three.only(Rules.single(limit, Chess.from_three(kind, board) <> Nil{}, moves))),
    Equal.cong(Finite.Table(width, Game.Outcome), Game.Outcome, table => Finite.get(width, Game.Outcome, Index.encode_at(width, board), table),
      Gen.select(width, kind, Gen.singles(limit, width, moves)), Gen.generate(limit, width, width, Gen.Single{kind}, moves, None{}),
      selected(limit, width, moves, kind)), single_pointwise(limit, width, size, moves, kind, board))

def rebuild(+material: FourIndex.Material, +turn: Game.Player, +wk: Word(6n), +bk: Word(6n),
  +owner: Game.Player, +first: Three.Material, +pc: Word(6n), +other: Game.Player, +second: Three.Material, +at: Word(6n),
  shape: Shape.Men(Chess.Man{owner, first, pc} <> Chess.Man{other, second, at} <> Nil{}, Gen.Double{material})) ->
  {FourIndex.position(material, FourIndex.Board{Three.Board{owner, turn, wk, bk, pc}, at}) ==
   Chess.Position{turn, wk, bk, Chess.Man{owner, first, pc} <> Chess.Man{other, second, at} <> Nil{}} : Chess.Position}:
  match material shape:
    case FourIndex.Material{+one, +two, +opposed} Shape.Both{a, Shape.Both{b, c}}:
      %Equal.sym(Three.Material, first, one, a) :
        {FourIndex.position(material, FourIndex.Board{Three.Board{owner, turn, wk, bk, pc}, at}) ==
         Chess.Position{turn, wk, bk, Chess.Man{owner, _, pc} <> Chess.Man{other, second, at} <> Nil{}} : Chess.Position}
      %Equal.sym(Three.Material, second, two, b) :
        {FourIndex.position(material, FourIndex.Board{Three.Board{owner, turn, wk, bk, pc}, at}) ==
         Chess.Position{turn, wk, bk, Chess.Man{owner, one, pc} <> Chess.Man{other, _, at} <> Nil{}} : Chess.Position}
      %Equal.sym(Game.Player, other, Bool.pick(Game.Player, opposed, Three.other(owner), owner), c) :
        {FourIndex.position(material, FourIndex.Board{Three.Board{owner, turn, wk, bk, pc}, at}) ==
         Chess.Position{turn, wk, bk, Chess.Man{owner, one, pc} <> Chess.Man{_, two, at} <> Nil{}} : Chess.Position}
      {==}

def double_at(+remaining: Nat, +width: Nat, +size: {width == 26n : Nat}, +low: Nat,
  +material: FourIndex.Material, +moves: Nat, +lower: Maybe<&2, Gen.Bundle<low>>, +board: FourIndex.Board,
  +position: Chess.Position, rebuilt: {FourIndex.position(material, board) == position : Chess.Position}) ->
  {Finite.get(width, Game.Outcome, FourIndex.encode_at(width, board), Gen.generate(remaining, width, low, Gen.Double{material}, moves, lower)) ==
   Gen.at(width, low, Gen.Double{material}, Gen.phase(remaining, width, low, Gen.Double{material}, moves, lower), lower, moves, position) : Game.Outcome}:
  generated_at(remaining, width, low, Gen.Double{material}, moves, lower, FourIndex.encode_at(width, board), position,
    Equal.trans(Chess.Position, Gen.decode(width, Gen.Double{material}, FourIndex.encode_at(width, board)),
      FourIndex.position(material, board), position,
      Equal.cong(FourIndex.Board, Chess.Position, b => FourIndex.position(material, b),
        FourIndex.decode_at(width, FourIndex.encode_at(width, board)), board, FourIndexProof.roundtrip_at(width, size, board)), rebuilt))

def double_step(+remaining: Nat, +width: Nat, +size: {width == 26n : Nat}, +low: Nat,
  +material: FourIndex.Material, +moves: Nat, +limit: Nat, +board: FourIndex.Board, +position: Chess.Position,
  rebuilt: {FourIndex.position(material, board) == position : Chess.Position},
  children:
    {Gen.values(Rules.children(Rules.view(moves, position)), width, low, Gen.Double{material},
       Gen.generate(remaining, width, low, Gen.Double{material}, moves, Some{Gen.singles(limit, low, moves)}), Some{Gen.singles(limit, low, moves)}) ==
     Lemmas.outcomes(Rules.forest(remaining, Rules.children(Rules.view(moves, position)), limit, moves)) : List<&2, Game.Outcome>}) ->
  {Finite.get(width, Game.Outcome, FourIndex.encode_at(width, board),
     Gen.generate(1n+remaining, width, low, Gen.Double{material}, moves, Some{Gen.singles(limit, low, moves)})) ==
   Game.evaluate(Rules.assemble(Rules.view(moves, position), Rules.forest(remaining, Rules.children(Rules.view(moves, position)), limit, moves))) : Game.Outcome}:
  +node = Rules.view(moves, position)
  +values = Gen.values(Rules.children(node), width, low, Gen.Double{material},
    Gen.generate(remaining, width, low, Gen.Double{material}, moves, Some{Gen.singles(limit, low, moves)}), Some{Gen.singles(limit, low, moves)})
  +trees = Rules.forest(remaining, Rules.children(node), limit, moves)
  Equal.trans(Game.Outcome,
    Finite.get(width, Game.Outcome, FourIndex.encode_at(width, board),
      Gen.generate(1n+remaining, width, low, Gen.Double{material}, moves, Some{Gen.singles(limit, low, moves)})),
    Gen.combine(node, values), Game.evaluate(Rules.assemble(node, trees)),
    double_at(1n+remaining, width, size, low, material, moves, Some{Gen.singles(limit, low, moves)}, board, position, rebuilt),
    combine_correct(node, values, trees, children))

# The fixed capture bundle is proved at limit, independently of the current
# reversible clock. Each quiet continuation uses the inductively proved layer.
def four_forest(remaining: Nat, +positions: List<&2, Chess.Position>, +width: Nat,
  +size: {width == 26n : Nat}, +low: Nat, +low_size: {low == 20n : Nat}, +moves: Nat,
  +limit: Nat, +material: FourIndex.Material, all: Shape.All(Gen.Double{material}, positions)) ->
  {Gen.values(positions, width, low, Gen.Double{material},
     Gen.generate(remaining, width, low, Gen.Double{material}, moves, Some{Gen.singles(limit, low, moves)}), Some{Gen.singles(limit, low, moves)}) ==
   Lemmas.outcomes(Rules.forest(remaining, positions, limit, moves)) : List<&2, Game.Outcome>}:
  match remaining positions material all:
    case 0n Nil{} _ _:
      {==}
    case 0n Chess.Position{turn, wk, bk, Nil{}} <> +tail _ Shape.Both{head, rest}:
      Lemmas.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        Gen.values(tail, width, low, Gen.Double{material}, Gen.generate(0n, width, low, Gen.Double{material}, moves, Some{Gen.singles(limit, low, moves)}), Some{Gen.singles(limit, low, moves)}), Lemmas.outcomes(Rules.forest(0n, tail, limit, moves)), {==}, four_forest(0n, tail, width, size, low, low_size, moves, limit, material, rest))
    case 0n Chess.Position{+turn, +wk, +bk, Chess.Man{+owner, +kind, +pc} <> Nil{}} <> +tail _ Shape.Both{head, rest}:
      +board = {Three.Board{owner, turn, wk, bk, pc} : Three.Board}
      Lemmas.cons_cong(Game.Outcome, Gen.lower_value(low, Some{Gen.singles(limit, low, moves)}, kind, board),
        Game.evaluate(Three.only(Rules.single(limit, Chess.from_three(kind, board) <> Nil{}, moves))),
        Gen.values(tail, width, low, Gen.Double{material}, Gen.generate(0n, width, low, Gen.Double{material}, moves, Some{Gen.singles(limit, low, moves)}), Some{Gen.singles(limit, low, moves)}), Lemmas.outcomes(Rules.forest(0n, tail, limit, moves)),
        lower_correct(limit, low, low_size, moves, kind, board), four_forest(0n, tail, width, size, low, low_size, moves, limit, material, rest))
    case 0n Chess.Position{+turn, +wk, +bk, Chess.Man{+owner, +first, +pc} <> Chess.Man{+other, +second, +at} <> Nil{}} <> +tail _ Shape.Both{+shape, rest}:
      +board = {FourIndex.Board{Three.Board{owner, turn, wk, bk, pc}, at} : FourIndex.Board}
      +position = {Chess.Position{turn, wk, bk, Chess.Man{owner, first, pc} <> Chess.Man{other, second, at} <> Nil{}} : Chess.Position}
      Lemmas.cons_cong(Game.Outcome, Finite.get(width, Game.Outcome, FourIndex.encode_at(width, board), Gen.generate(0n, width, low, Gen.Double{material}, moves, Some{Gen.singles(limit, low, moves)})),
        Game.evaluate(Three.only(Rules.forest(0n, position <> Nil{}, limit, moves))),
        Gen.values(tail, width, low, Gen.Double{material}, Gen.generate(0n, width, low, Gen.Double{material}, moves, Some{Gen.singles(limit, low, moves)}), Some{Gen.singles(limit, low, moves)}), Lemmas.outcomes(Rules.forest(0n, tail, limit, moves)),
        double_at(0n, width, size, low, material, moves, Some{Gen.singles(limit, low, moves)}, board, position,
          rebuild(material, turn, wk, bk, owner, first, pc, other, second, at, shape)),
        four_forest(0n, tail, width, size, low, low_size, moves, limit, material, rest))
    case 0n Chess.Position{turn, wk, bk, Chess.Man{oa, ka, xa} <> Chess.Man{ob, kb, xb} <> c <> men} <> tail FourIndex.Material{one, two, opposed} Shape.Both{bad, rest}:
      match bad:
    case 1n++clock Nil{} _ _:
      {==}
    case 1n++clock Chess.Position{turn, wk, bk, Nil{}} <> +tail _ Shape.Both{head, rest}:
      Lemmas.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        Gen.values(tail, width, low, Gen.Double{material}, Gen.generate(1n+clock, width, low, Gen.Double{material}, moves, Some{Gen.singles(limit, low, moves)}), Some{Gen.singles(limit, low, moves)}), Lemmas.outcomes(Rules.forest(1n+clock, tail, limit, moves)), {==}, four_forest(1n+clock, tail, width, size, low, low_size, moves, limit, material, rest))
    case 1n++clock Chess.Position{+turn, +wk, +bk, Chess.Man{+owner, +kind, +pc} <> Nil{}} <> +tail _ Shape.Both{head, rest}:
      +board = {Three.Board{owner, turn, wk, bk, pc} : Three.Board}
      Lemmas.cons_cong(Game.Outcome, Gen.lower_value(low, Some{Gen.singles(limit, low, moves)}, kind, board),
        Game.evaluate(Three.only(Rules.single(limit, Chess.from_three(kind, board) <> Nil{}, moves))),
        Gen.values(tail, width, low, Gen.Double{material}, Gen.generate(1n+clock, width, low, Gen.Double{material}, moves, Some{Gen.singles(limit, low, moves)}), Some{Gen.singles(limit, low, moves)}), Lemmas.outcomes(Rules.forest(1n+clock, tail, limit, moves)),
        lower_correct(limit, low, low_size, moves, kind, board), four_forest(1n+clock, tail, width, size, low, low_size, moves, limit, material, rest))
    case 1n++clock Chess.Position{+turn, +wk, +bk, Chess.Man{+owner, +first, +pc} <> Chess.Man{+other, +second, +at} <> Nil{}} <> +tail _ Shape.Both{+shape, rest}:
      +board = {FourIndex.Board{Three.Board{owner, turn, wk, bk, pc}, at} : FourIndex.Board}
      +position = {Chess.Position{turn, wk, bk, Chess.Man{owner, first, pc} <> Chess.Man{other, second, at} <> Nil{}} : Chess.Position}
      Lemmas.cons_cong(Game.Outcome, Finite.get(width, Game.Outcome, FourIndex.encode_at(width, board), Gen.generate(1n+clock, width, low, Gen.Double{material}, moves, Some{Gen.singles(limit, low, moves)})),
        Game.evaluate(Three.only(Rules.forest(1n+clock, position <> Nil{}, limit, moves))),
        Gen.values(tail, width, low, Gen.Double{material}, Gen.generate(1n+clock, width, low, Gen.Double{material}, moves, Some{Gen.singles(limit, low, moves)}), Some{Gen.singles(limit, low, moves)}), Lemmas.outcomes(Rules.forest(1n+clock, tail, limit, moves)),
        double_step(clock, width, size, low, material, moves, limit, board, position,
          rebuild(material, turn, wk, bk, owner, first, pc, other, second, at, shape),
          four_forest(clock, Rules.children(Rules.view(moves, position)), width, size, low, low_size, moves, limit, material,
            Shape.children(moves, Gen.Double{material}, position, shape))),
        four_forest(1n+clock, tail, width, size, low, low_size, moves, limit, material, rest))
    case 1n++clock Chess.Position{turn, wk, bk, Chess.Man{oa, ka, xa} <> Chess.Man{ob, kb, xb} <> c <> men} <> tail FourIndex.Material{one, two, opposed} Shape.Both{bad, rest}:
      match bad:

def pointwise(+limit: Nat, +width: Nat, +size: {width == 26n : Nat}, +low: Nat,
  +low_size: {low == 20n : Nat}, +moves: Nat, +material: FourIndex.Material, +board: FourIndex.Board) ->
  {Finite.get(width, Game.Outcome, FourIndex.encode_at(width, board), Gen.four(limit, width, low, moves, material)) ==
   Game.evaluate(Rules.tree(limit, moves, FourIndex.position(material, board))) : Game.Outcome}:
  match material board:
    case FourIndex.Material{first, second, opposed} FourIndex.Board{Three.Board{owner, turn, wk, bk, pc}, at}:
      +position = FourIndex.position(material, board)
      +positions = {position <> Nil{} : List<&2, Chess.Position>}
      only_correct(
        Gen.values(positions, width, low, Gen.Double{material},
          Gen.generate(limit, width, low, Gen.Double{material}, moves, Some{Gen.singles(limit, low, moves)}), Some{Gen.singles(limit, low, moves)}),
        Rules.forest(limit, positions, limit, moves),
        four_forest(limit, positions, width, size, low, low_size, moves, limit, material,
          Shape.Both{Shape.Both{{==}, Shape.Both{{==}, {==}}}, Unit{}}))

def serialized_value(+limit: Nat, +width: Nat, +size: {width == 26n : Nat}, +low: Nat,
  +low_size: {low == 20n : Nat}, +moves: Nat, +material: FourIndex.Material, +board: FourIndex.Board) ->
  {Finite.read(Gen.file(limit, width, low, moves, material), Finite.offset(width, FourIndex.encode_at(width, board))) ==
   Some{Game.byte(Game.evaluate(Rules.tree(limit, moves, FourIndex.position(material, board))))} : Maybe<&2, U32>}:
  +table = Gen.four(limit, width, low, moves, material)
  +key = FourIndex.encode_at(width, board)
  +stored = Finite.get(width, U32, key, Bytes.bytes(width, table))
  +value = Finite.get(width, Game.Outcome, key, table)
  +expected = Game.evaluate(Rules.tree(limit, moves, FourIndex.position(material, board)))
  Equal.trans(Maybe<&2, U32>, Finite.read(Gen.file(limit, width, low, moves, material), Finite.offset(width, key)),
    Some{stored}, Some{Game.byte(expected)}, FiniteProof.read_go(width, Bytes.bytes(width, table), key, Nil{}),
    Equal.trans(Maybe<&2, U32>, Some{stored}, Some{Game.byte(value)}, Some{Game.byte(expected)},
      Equal.cong(U32, Maybe<&2, U32>, byte => Some{byte}, stored, Game.byte(value), Lemmas.bytes_get(width, table, key)),
      Equal.cong(Game.Outcome, Maybe<&2, U32>, outcome => Some{Game.byte(outcome)}, value, expected,
        pointwise(limit, width, size, low, low_size, moves, material, board))))

def file_length(+limit: Nat, +width: Nat, +low: Nat, +moves: Nat, +material: FourIndex.Material) ->
  {List.length(&2, U32, Gen.file(limit, width, low, moves, material)) == Finite.size(width) : Nat}:
  Equal.trans(Nat, List.length(&2, U32, Gen.file(limit, width, low, moves, material)), Nat.add(Finite.size(width), 0n), Finite.size(width),
    FiniteProof.length_go(width, Bytes.bytes(width, Gen.four(limit, width, low, moves, material)), Nil{}),
    Lemmas.add_zero(Finite.size(width)))
