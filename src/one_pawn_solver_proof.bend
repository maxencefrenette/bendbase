import Base
import ./game.bend as Game
import ./pawnless_chess.bend as Three
import ./pawn_chess.bend as Pawn
import ./one_pawn_chess.bend as Chess
import ./one_pawn_game.bend as Rules
import ./one_pawn_solver.bend as Solver
import ./four_chess.bend as Four
import ./four_solver.bend as FourSolver
import ./four_solver_proof.bend as FourProof
import ./pawnless_tables.bend as Fold
import ./pawnless_tables_proof.bend as Lemmas

def assemble_evaluate(+node: Rules.View, +trees: List<&2, Game.Tree>) ->
  {Solver.combine(node, Lemmas.outcomes(trees)) == Game.evaluate(Rules.assemble(node, trees)) : Game.Outcome}:
  match node trees:
    case Rules.Stop{outcome} _:
      {==}
    case Rules.Play{turn, edges} Nil{}:
      {==}
    case Rules.Play{+turn, edges} +head <> +tail:
      Equal.sym(Game.Outcome, Game.evaluate(Three.choices(tail, turn, head)),
        Fold.fold(Lemmas.outcomes(tail), turn, Game.evaluate(head)),
        Lemmas.choices_evaluate(tail, turn, head))

def combine_correct(+node: Rules.View, +values: List<&2, Game.Outcome>, +trees: List<&2, Game.Tree>,
  correct: {values == Lemmas.outcomes(trees) : List<&2, Game.Outcome>}) ->
  {Solver.combine(node, values) == Game.evaluate(Rules.assemble(node, trees)) : Game.Outcome}:
  Equal.trans(Game.Outcome, Solver.combine(node, values), Solver.combine(node, Lemmas.outcomes(trees)),
    Game.evaluate(Rules.assemble(node, trees)),
    Equal.cong(List<&2, Game.Outcome>, Game.Outcome, xs => Solver.combine(node, xs),
      values, Lemmas.outcomes(trees), correct), assemble_evaluate(node, trees))

# Induction over actual pawn rank, clock, expansion stage and an arbitrary
# list. Neither the move lists nor the board squares are enumerated.
def forest_correct(+advance: Nat, +remaining: Nat, +stage: Nat, +items: List<&2, Rules.Task>,
  +limit: Nat, +moves: Nat, +other_moves: Nat) ->
  {Solver.forest(advance, remaining, stage, items, limit, moves, other_moves) ==
   Lemmas.outcomes(Rules.forest(advance, remaining, stage, items, limit, moves, other_moves)) : List<&2, Game.Outcome>}:
  match advance remaining stage items:
    case 0n _ _ Nil{}:
      {==}
    case 0n _ _ head <> +tail:
      Lemmas.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        Solver.forest(0n, remaining, stage, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(0n, remaining, stage, tail, limit, moves, other_moves)),
        {==}, forest_correct(0n, remaining, stage, tail, limit, moves, other_moves))
    case 1n 0n 0n Nil{}:
      {==}
    case 1n 0n 0n head <> +tail:
      Lemmas.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        Solver.forest(1n, 0n, 0n, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n, 0n, 0n, tail, limit, moves, other_moves)),
        {==}, forest_correct(1n, 0n, 0n, tail, limit, moves, other_moves))
    case 1n 0n 1n Nil{}:
      {==}
    case 1n 0n 1n Rules.Follow{edge} <> +tail:
      Lemmas.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        Solver.forest(1n, 0n, 1n, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n, 0n, 1n, tail, limit, moves, other_moves)),
        {==}, forest_correct(1n, 0n, 1n, tail, limit, moves, other_moves))
    case 1n 0n 1n Rules.Here{+position} <> +tail:
      +node = Rules.view(moves, 1n, position)
      Lemmas.cons_cong(Game.Outcome, Game.evaluate(Rules.boundary(node)), Game.evaluate(Rules.boundary(node)),
        Solver.forest(1n, 0n, 1n, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n, 0n, 1n, tail, limit, moves, other_moves)),
        {==}, forest_correct(1n, 0n, 1n, tail, limit, moves, other_moves))
    case 1n 0n 1n+1n++extra Nil{}:
      {==}
    case 1n 0n 1n+1n++extra head <> +tail:
      Lemmas.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        Solver.forest(1n, 0n, 1n+1n+extra, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n, 0n, 1n+1n+extra, tail, limit, moves, other_moves)),
        {==}, forest_correct(1n, 0n, 1n+1n+extra, tail, limit, moves, other_moves))
    case 1n 1n++clock 0n Nil{}:
      {==}
    case 1n 1n++clock 0n Rules.Here{position} <> +tail:
      Lemmas.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        Solver.forest(1n, 1n+clock, 0n, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n, 1n+clock, 0n, tail, limit, moves, other_moves)),
        {==}, forest_correct(1n, 1n+clock, 0n, tail, limit, moves, other_moves))
    case 1n 1n++clock 0n Rules.Follow{Chess.Quiet{+position}} <> +tail:
      Lemmas.cons_cong(Game.Outcome, FourSolver.first(Solver.forest(1n, clock, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves)), Game.evaluate(Three.only(Rules.forest(1n, clock, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves))),
        Solver.forest(1n, 1n+clock, 0n, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n, 1n+clock, 0n, tail, limit, moves, other_moves)),
        FourProof.only_correct(Solver.forest(1n, clock, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves), Rules.forest(1n, clock, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves),
          forest_correct(1n, clock, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves)), forest_correct(1n, 1n+clock, 0n, tail, limit, moves, other_moves))
    case 1n 1n++clock 0n Rules.Follow{Chess.Push{+position}} <> +tail:
      Lemmas.cons_cong(Game.Outcome, FourSolver.first(Solver.forest(0n, limit, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves)), Game.evaluate(Three.only(Rules.forest(0n, limit, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves))),
        Solver.forest(1n, 1n+clock, 0n, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n, 1n+clock, 0n, tail, limit, moves, other_moves)),
        FourProof.only_correct(Solver.forest(0n, limit, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves), Rules.forest(0n, limit, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves),
          forest_correct(0n, limit, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves)), forest_correct(1n, 1n+clock, 0n, tail, limit, moves, other_moves))
    case 1n 1n++clock 0n Rules.Follow{Chess.DoublePush{+position}} <> +tail:
      Lemmas.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        Solver.forest(1n, 1n+clock, 0n, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n, 1n+clock, 0n, tail, limit, moves, other_moves)),
        {==}, forest_correct(1n, 1n+clock, 0n, tail, limit, moves, other_moves))
    case 1n 1n++clock 0n Rules.Follow{Chess.KPK{+board}} <> +tail:
      Lemmas.cons_cong(Game.Outcome, Game.evaluate(Pawn.tree(limit, board)), Game.evaluate(Pawn.tree(limit, board)),
        Solver.forest(1n, 1n+clock, 0n, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n, 1n+clock, 0n, tail, limit, moves, other_moves)),
        {==}, forest_correct(1n, 1n+clock, 0n, tail, limit, moves, other_moves))
    case 1n 1n++clock 0n Rules.Follow{Chess.Pawnless{+position}} <> +tail:
      Lemmas.cons_cong(Game.Outcome, FourSolver.value(limit, other_moves, position), Game.evaluate(Four.tree(limit, other_moves, position)),
        Solver.forest(1n, 1n+clock, 0n, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n, 1n+clock, 0n, tail, limit, moves, other_moves)),
        FourProof.pointwise(limit, other_moves, position), forest_correct(1n, 1n+clock, 0n, tail, limit, moves, other_moves))
    case 1n 1n++clock 1n Nil{}:
      {==}
    case 1n 1n++clock 1n Rules.Follow{edge} <> +tail:
      Lemmas.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        Solver.forest(1n, 1n+clock, 1n, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n, 1n+clock, 1n, tail, limit, moves, other_moves)),
        {==}, forest_correct(1n, 1n+clock, 1n, tail, limit, moves, other_moves))
    case 1n 1n++clock 1n Rules.Here{+position} <> +tail:
      +node = Rules.view(moves, 1n, position)
      Lemmas.cons_cong(Game.Outcome, Solver.combine(node, Solver.forest(1n, 1n+clock, 0n, Rules.tasks(node), limit, moves, other_moves)), Game.evaluate(Rules.assemble(node, Rules.forest(1n, 1n+clock, 0n, Rules.tasks(node), limit, moves, other_moves))),
        Solver.forest(1n, 1n+clock, 1n, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n, 1n+clock, 1n, tail, limit, moves, other_moves)),
        combine_correct(node, Solver.forest(1n, 1n+clock, 0n, Rules.tasks(node), limit, moves, other_moves),
          Rules.forest(1n, 1n+clock, 0n, Rules.tasks(node), limit, moves, other_moves),
          forest_correct(1n, 1n+clock, 0n, Rules.tasks(node), limit, moves, other_moves)), forest_correct(1n, 1n+clock, 1n, tail, limit, moves, other_moves))
    case 1n 1n++clock 1n+1n++extra Nil{}:
      {==}
    case 1n 1n++clock 1n+1n++extra head <> +tail:
      Lemmas.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        Solver.forest(1n, 1n+clock, 1n+1n+extra, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n, 1n+clock, 1n+1n+extra, tail, limit, moves, other_moves)),
        {==}, forest_correct(1n, 1n+clock, 1n+1n+extra, tail, limit, moves, other_moves))
    case 1n+1n++prior 0n 0n Nil{}:
      {==}
    case 1n+1n++prior 0n 0n head <> +tail:
      Lemmas.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        Solver.forest(1n+1n+prior, 0n, 0n, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n+1n+prior, 0n, 0n, tail, limit, moves, other_moves)),
        {==}, forest_correct(1n+1n+prior, 0n, 0n, tail, limit, moves, other_moves))
    case 1n+1n++prior 0n 1n Nil{}:
      {==}
    case 1n+1n++prior 0n 1n Rules.Follow{edge} <> +tail:
      Lemmas.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        Solver.forest(1n+1n+prior, 0n, 1n, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n+1n+prior, 0n, 1n, tail, limit, moves, other_moves)),
        {==}, forest_correct(1n+1n+prior, 0n, 1n, tail, limit, moves, other_moves))
    case 1n+1n++prior 0n 1n Rules.Here{+position} <> +tail:
      +node = Rules.view(moves, 1n+1n+prior, position)
      Lemmas.cons_cong(Game.Outcome, Game.evaluate(Rules.boundary(node)), Game.evaluate(Rules.boundary(node)),
        Solver.forest(1n+1n+prior, 0n, 1n, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n+1n+prior, 0n, 1n, tail, limit, moves, other_moves)),
        {==}, forest_correct(1n+1n+prior, 0n, 1n, tail, limit, moves, other_moves))
    case 1n+1n++prior 0n 1n+1n++extra Nil{}:
      {==}
    case 1n+1n++prior 0n 1n+1n++extra head <> +tail:
      Lemmas.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        Solver.forest(1n+1n+prior, 0n, 1n+1n+extra, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n+1n+prior, 0n, 1n+1n+extra, tail, limit, moves, other_moves)),
        {==}, forest_correct(1n+1n+prior, 0n, 1n+1n+extra, tail, limit, moves, other_moves))
    case 1n+1n++prior 1n++clock 0n Nil{}:
      {==}
    case 1n+1n++prior 1n++clock 0n Rules.Here{position} <> +tail:
      Lemmas.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        Solver.forest(1n+1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n+1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves)),
        {==}, forest_correct(1n+1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves))
    case 1n+1n++prior 1n++clock 0n Rules.Follow{Chess.Quiet{+position}} <> +tail:
      Lemmas.cons_cong(Game.Outcome, FourSolver.first(Solver.forest(1n+1n+prior, clock, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves)), Game.evaluate(Three.only(Rules.forest(1n+1n+prior, clock, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves))),
        Solver.forest(1n+1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n+1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves)),
        FourProof.only_correct(Solver.forest(1n+1n+prior, clock, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves), Rules.forest(1n+1n+prior, clock, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves),
          forest_correct(1n+1n+prior, clock, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves)), forest_correct(1n+1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves))
    case 1n+1n++prior 1n++clock 0n Rules.Follow{Chess.Push{+position}} <> +tail:
      Lemmas.cons_cong(Game.Outcome, FourSolver.first(Solver.forest(1n+prior, limit, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves)), Game.evaluate(Three.only(Rules.forest(1n+prior, limit, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves))),
        Solver.forest(1n+1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n+1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves)),
        FourProof.only_correct(Solver.forest(1n+prior, limit, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves), Rules.forest(1n+prior, limit, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves),
          forest_correct(1n+prior, limit, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves)), forest_correct(1n+1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves))
    case 1n+1n++prior 1n++clock 0n Rules.Follow{Chess.DoublePush{+position}} <> +tail:
      Lemmas.cons_cong(Game.Outcome, FourSolver.first(Solver.forest(prior, limit, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves)), Game.evaluate(Three.only(Rules.forest(prior, limit, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves))),
        Solver.forest(1n+1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n+1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves)),
        FourProof.only_correct(Solver.forest(prior, limit, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves), Rules.forest(prior, limit, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves),
          forest_correct(prior, limit, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves)), forest_correct(1n+1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves))
    case 1n+1n++prior 1n++clock 0n Rules.Follow{Chess.KPK{+board}} <> +tail:
      Lemmas.cons_cong(Game.Outcome, Game.evaluate(Pawn.tree(limit, board)), Game.evaluate(Pawn.tree(limit, board)),
        Solver.forest(1n+1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n+1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves)),
        {==}, forest_correct(1n+1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves))
    case 1n+1n++prior 1n++clock 0n Rules.Follow{Chess.Pawnless{+position}} <> +tail:
      Lemmas.cons_cong(Game.Outcome, FourSolver.value(limit, other_moves, position), Game.evaluate(Four.tree(limit, other_moves, position)),
        Solver.forest(1n+1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n+1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves)),
        FourProof.pointwise(limit, other_moves, position), forest_correct(1n+1n+prior, 1n+clock, 0n, tail, limit, moves, other_moves))
    case 1n+1n++prior 1n++clock 1n Nil{}:
      {==}
    case 1n+1n++prior 1n++clock 1n Rules.Follow{edge} <> +tail:
      Lemmas.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        Solver.forest(1n+1n+prior, 1n+clock, 1n, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n+1n+prior, 1n+clock, 1n, tail, limit, moves, other_moves)),
        {==}, forest_correct(1n+1n+prior, 1n+clock, 1n, tail, limit, moves, other_moves))
    case 1n+1n++prior 1n++clock 1n Rules.Here{+position} <> +tail:
      +node = Rules.view(moves, 1n+1n+prior, position)
      Lemmas.cons_cong(Game.Outcome, Solver.combine(node, Solver.forest(1n+1n+prior, 1n+clock, 0n, Rules.tasks(node), limit, moves, other_moves)), Game.evaluate(Rules.assemble(node, Rules.forest(1n+1n+prior, 1n+clock, 0n, Rules.tasks(node), limit, moves, other_moves))),
        Solver.forest(1n+1n+prior, 1n+clock, 1n, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n+1n+prior, 1n+clock, 1n, tail, limit, moves, other_moves)),
        combine_correct(node, Solver.forest(1n+1n+prior, 1n+clock, 0n, Rules.tasks(node), limit, moves, other_moves),
          Rules.forest(1n+1n+prior, 1n+clock, 0n, Rules.tasks(node), limit, moves, other_moves),
          forest_correct(1n+1n+prior, 1n+clock, 0n, Rules.tasks(node), limit, moves, other_moves)), forest_correct(1n+1n+prior, 1n+clock, 1n, tail, limit, moves, other_moves))
    case 1n+1n++prior 1n++clock 1n+1n++extra Nil{}:
      {==}
    case 1n+1n++prior 1n++clock 1n+1n++extra head <> +tail:
      Lemmas.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        Solver.forest(1n+1n+prior, 1n+clock, 1n+1n+extra, tail, limit, moves, other_moves),
        Lemmas.outcomes(Rules.forest(1n+1n+prior, 1n+clock, 1n+1n+extra, tail, limit, moves, other_moves)),
        {==}, forest_correct(1n+1n+prior, 1n+clock, 1n+1n+extra, tail, limit, moves, other_moves))

def pointwise(+limit: Nat, +moves: Nat, +other_moves: Nat, +advance: Nat, +position: Chess.Position) ->
  {Solver.value(limit, moves, other_moves, advance, position) ==
   Game.evaluate(Rules.tree(limit, moves, other_moves, advance, position)) : Game.Outcome}:
  FourProof.only_correct(Solver.forest(advance, limit, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves),
    Rules.forest(advance, limit, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves),
    forest_correct(advance, limit, 1n, Rules.Here{position} <> Nil{}, limit, moves, other_moves))
