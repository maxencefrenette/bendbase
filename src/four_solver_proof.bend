import Base
import ./game.bend as Game
import ./pawnless_chess.bend as Three
import ./material_chess.bend as Chess
import ./four_chess.bend as Rules
import ./four_solver.bend as Solver
import ./pawnless_tables.bend as Tables
import ./pawnless_tables_proof.bend as Lemmas

def assemble_evaluate(+node: Rules.View, +trees: List<&2, Game.Tree>) ->
  {Solver.combine(node, Lemmas.outcomes(trees)) == Game.evaluate(Rules.assemble(node, trees)) : Game.Outcome}:
  match node trees:
    case Rules.Stop{result} _:
      {==}
    case Rules.Play{turn, children} Nil{}:
      {==}
    case Rules.Play{+turn, children} +head <> +tail:
      Equal.sym(Game.Outcome, Game.evaluate(Three.choices(tail, turn, head)),
        Tables.fold(Lemmas.outcomes(tail), turn, Game.evaluate(head)),
        Lemmas.choices_evaluate(tail, turn, head))

def combine_correct(+node: Rules.View, +values: List<&2, Game.Outcome>, +trees: List<&2, Game.Tree>,
  correct: {values == Lemmas.outcomes(trees) : List<&2, Game.Outcome>}) ->
  {Solver.combine(node, values) == Game.evaluate(Rules.assemble(node, trees)) : Game.Outcome}:
  Equal.trans(Game.Outcome, Solver.combine(node, values), Solver.combine(node, Lemmas.outcomes(trees)),
    Game.evaluate(Rules.assemble(node, trees)),
    Equal.cong(List<&2, Game.Outcome>, Game.Outcome, xs => Solver.combine(node, xs),
      values, Lemmas.outcomes(trees), correct), assemble_evaluate(node, trees))

def first_outcomes(+trees: List<&2, Game.Tree>) ->
  {Solver.first(Lemmas.outcomes(trees)) == Game.evaluate(Three.only(trees)) : Game.Outcome}:
  match trees:
    case Nil{}:
      {==}
    case head <> tail:
      {==}

def only_correct(+values: List<&2, Game.Outcome>, +trees: List<&2, Game.Tree>,
  correct: {values == Lemmas.outcomes(trees) : List<&2, Game.Outcome>}) ->
  {Solver.first(values) == Game.evaluate(Three.only(trees)) : Game.Outcome}:
  Equal.trans(Game.Outcome, Solver.first(values), Solver.first(Lemmas.outcomes(trees)),
    Game.evaluate(Three.only(trees)),
    Equal.cong(List<&2, Game.Outcome>, Game.Outcome, xs => Solver.first(xs),
      values, Lemmas.outcomes(trees), correct), first_outcomes(trees))

def single_correct(remaining: Nat, +positions: List<&2, Chess.Position>, +moves: Nat) ->
  {Solver.single(remaining, positions, moves) == Lemmas.outcomes(Rules.single(remaining, positions, moves)) : List<&2, Game.Outcome>}:
  match remaining positions:
    case 0n Nil{}:
      {==}
    case 1n+clock Nil{}:
      {==}
    case 0n +head <> +tail:
      +value = Game.evaluate(Rules.boundary(Rules.view(moves, head)))
      Lemmas.cons_cong(Game.Outcome, value, value, Solver.single(0n, tail, moves),
        Lemmas.outcomes(Rules.single(0n, tail, moves)), {==}, single_correct(0n, tail, moves))
    case 1n++clock +head <> +tail:
      +node = Rules.view(moves, head)
      +values = Solver.single(clock, Rules.children(node), moves)
      +trees = Rules.single(clock, Rules.children(node), moves)
      Lemmas.cons_cong(Game.Outcome, Solver.combine(node, values), Game.evaluate(Rules.assemble(node, trees)),
        Solver.single(1n+clock, tail, moves), Lemmas.outcomes(Rules.single(1n+clock, tail, moves)),
        combine_correct(node, values, trees, single_correct(clock, Rules.children(node), moves)),
        single_correct(1n+clock, tail, moves))

def forest_correct(remaining: Nat, +positions: List<&2, Chess.Position>, +limit: Nat, +moves: Nat) ->
  {Solver.forest(remaining, positions, limit, moves) == Lemmas.outcomes(Rules.forest(remaining, positions, limit, moves)) : List<&2, Game.Outcome>}:
  match remaining positions:
    case 0n Nil{}:
      {==}
    case 0n Chess.Position{+turn, +wk, +bk, Nil{}} <> +tail:
      Lemmas.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        Solver.forest(0n, tail, limit, moves), Lemmas.outcomes(Rules.forest(0n, tail, limit, moves)),
        {==}, forest_correct(0n, tail, limit, moves))
    case 0n Chess.Position{+turn, +wk, +bk, +man <> Nil{}} <> +tail:
      +position = {Chess.Position{turn, wk, bk, man <> Nil{}} : Chess.Position}
      Lemmas.cons_cong(Game.Outcome, Solver.first(Solver.single(limit, position <> Nil{}, moves)), Game.evaluate(Three.only(Rules.single(limit, position <> Nil{}, moves))),
        Solver.forest(0n, tail, limit, moves), Lemmas.outcomes(Rules.forest(0n, tail, limit, moves)),
        only_correct(Solver.single(limit, position <> Nil{}, moves), Rules.single(limit, position <> Nil{}, moves), single_correct(limit, position <> Nil{}, moves)), forest_correct(0n, tail, limit, moves))
    case 0n Chess.Position{+turn, +wk, +bk, +a <> +b <> Nil{}} <> +tail:
      +position = {Chess.Position{turn, wk, bk, a <> b <> Nil{}} : Chess.Position}
      +node = Rules.view(moves, position)
      Lemmas.cons_cong(Game.Outcome, Game.evaluate(Rules.boundary(node)), Game.evaluate(Rules.boundary(node)),
        Solver.forest(0n, tail, limit, moves), Lemmas.outcomes(Rules.forest(0n, tail, limit, moves)),
        {==}, forest_correct(0n, tail, limit, moves))
    case 0n Chess.Position{+turn, +wk, +bk, +a <> +b <> +c <> +rest} <> +tail:
      Lemmas.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        Solver.forest(0n, tail, limit, moves), Lemmas.outcomes(Rules.forest(0n, tail, limit, moves)),
        {==}, forest_correct(0n, tail, limit, moves))
    case 1n++clock Nil{}:
      {==}
    case 1n++clock Chess.Position{+turn, +wk, +bk, Nil{}} <> +tail:
      Lemmas.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        Solver.forest(1n+clock, tail, limit, moves), Lemmas.outcomes(Rules.forest(1n+clock, tail, limit, moves)),
        {==}, forest_correct(1n+clock, tail, limit, moves))
    case 1n++clock Chess.Position{+turn, +wk, +bk, +man <> Nil{}} <> +tail:
      +position = {Chess.Position{turn, wk, bk, man <> Nil{}} : Chess.Position}
      Lemmas.cons_cong(Game.Outcome, Solver.first(Solver.single(limit, position <> Nil{}, moves)), Game.evaluate(Three.only(Rules.single(limit, position <> Nil{}, moves))),
        Solver.forest(1n+clock, tail, limit, moves), Lemmas.outcomes(Rules.forest(1n+clock, tail, limit, moves)),
        only_correct(Solver.single(limit, position <> Nil{}, moves), Rules.single(limit, position <> Nil{}, moves), single_correct(limit, position <> Nil{}, moves)), forest_correct(1n+clock, tail, limit, moves))
    case 1n++clock Chess.Position{+turn, +wk, +bk, +a <> +b <> Nil{}} <> +tail:
      +position = {Chess.Position{turn, wk, bk, a <> b <> Nil{}} : Chess.Position}
      +node = Rules.view(moves, position)
      Lemmas.cons_cong(Game.Outcome, Solver.combine(node, Solver.forest(clock, Rules.children(node), limit, moves)), Game.evaluate(Rules.assemble(node, Rules.forest(clock, Rules.children(node), limit, moves))),
        Solver.forest(1n+clock, tail, limit, moves), Lemmas.outcomes(Rules.forest(1n+clock, tail, limit, moves)),
        combine_correct(node, Solver.forest(clock, Rules.children(node), limit, moves), Rules.forest(clock, Rules.children(node), limit, moves), forest_correct(clock, Rules.children(node), limit, moves)), forest_correct(1n+clock, tail, limit, moves))
    case 1n++clock Chess.Position{+turn, +wk, +bk, +a <> +b <> +c <> +rest} <> +tail:
      Lemmas.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        Solver.forest(1n+clock, tail, limit, moves), Lemmas.outcomes(Rules.forest(1n+clock, tail, limit, moves)),
        {==}, forest_correct(1n+clock, tail, limit, moves))

def pointwise(+limit: Nat, +moves: Nat, +position: Chess.Position) ->
  {Solver.value(limit, moves, position) == Game.evaluate(Rules.tree(limit, moves, position)) : Game.Outcome}:
  only_correct(Solver.forest(limit, position <> Nil{}, limit, moves), Rules.forest(limit, position <> Nil{}, limit, moves),
    forest_correct(limit, position <> Nil{}, limit, moves))
