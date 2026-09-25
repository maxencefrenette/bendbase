import Base
import ./chess_game.bend as Semantics
import ./chess.bend as Chess
import ./chess_measure.bend as Measure
import ./chess_measure_proof.bend as MeasureProof
import ./chess_selection_proof.bend as Selection
import ./position.bend as P
import ./game.bend as Game
import ./chess_graph.bend as Graph
import ./chess_game_total.bend as Total
import ./pawnless_chess.bend as Choices
import ./pawnless_tables_proof.bend as Lemmas

# Fuel is only a termination device. Two complete unfoldings are the same
# tree, not merely games with the same outcome. Induction follows arbitrary
# fuel and state-list constructors; it never enumerates chess positions.
def fuel_independent(+left: Nat, +right: Nat, +items: List<&2, Semantics.State>, +limit: Nat, +actions: Nat,
  first: Semantics.NoCutoff(left, items, limit, actions),
  second: Semantics.NoCutoff(right, items, limit, actions)) ->
  {Semantics.forest(left, items, limit, actions) == Semantics.forest(right, items, limit, actions) : List<&2, Game.Tree>}:
  match left right items:
    case 0n 0n Nil{}:
      {==}
    case 0n 1n+other Nil{}:
      {==}
    case 1n+prior 0n Nil{}:
      {==}
    case 1n+prior 1n+other Nil{}:
      {==}
    case 0n _ head <> tail:
      match first:
    case 1n+prior 0n head <> tail:
      match second:
    case 1n++prior 1n++other Semantics.State{0n, board} <> tail:
      Equal.cong(List<&2, Game.Tree>, List<&2, Game.Tree>, more => Game.End{Chess.boundary(Chess.view(actions, board))} <> more,
        Semantics.forest(1n+prior, tail, limit, actions), Semantics.forest(1n+other, tail, limit, actions),
        fuel_independent(1n+prior, 1n+other, tail, limit, actions, first, second))
    case 1n++prior 1n++other Semantics.State{1n+clock, +board} <> tail:
      (child_first, tail_first) = first
      (child_second, tail_second) = second
      +node = Graph.node(actions, Game.White{}, board)
      +next = Semantics.states(limit, 1n+clock, Semantics.children(node))
      Lemmas.cons_cong(Game.Tree,
        Semantics.assemble(node, Semantics.forest(prior, next, limit, actions)),
        Semantics.assemble(node, Semantics.forest(other, next, limit, actions)),
        Semantics.forest(1n+prior, tail, limit, actions), Semantics.forest(1n+other, tail, limit, actions),
        Equal.cong(List<&2, Game.Tree>, Game.Tree, trees => Semantics.assemble(node, trees),
          Semantics.forest(prior, next, limit, actions), Semantics.forest(other, next, limit, actions),
          fuel_independent(prior, other, next, limit, actions, child_first, child_second)),
        fuel_independent(1n+prior, 1n+other, tail, limit, actions, tail_first, tail_second))

# A continuation unfolded with its parent's fuel agrees with the canonical
# standalone game. This is what makes reuse of a cached destination sound.
def canonical(+fuel: Nat, +limit: Nat, +remaining: Nat, +board: P.Position,
  complete: Semantics.NoCutoff(fuel, [Semantics.State{remaining, board}], limit, 14n)) ->
  {Choices.only(Semantics.forest(fuel, [Semantics.State{remaining, board}], limit, 14n)) ==
   Semantics.tree(limit, remaining, board) : Game.Tree}:
  Equal.cong(List<&2, Game.Tree>, Game.Tree, trees => Choices.only(trees),
    Semantics.forest(fuel, [Semantics.State{remaining, board}], limit, 14n),
    Semantics.forest(Measure.budget(limit, Measure.position(board), remaining), [Semantics.State{remaining, board}], limit, 14n),
    fuel_independent(fuel, Measure.budget(limit, Measure.position(board), remaining),
      [Semantics.State{remaining, board}], limit, 14n, complete, Total.complete(limit, remaining, 14n, board)))

def standalone(+fuel: Nat, +items: List<&2, Semantics.State>, +limit: Nat,
  complete: Semantics.NoCutoff(fuel, items, limit, 14n)) ->
  {Semantics.forest(fuel, items, limit, 14n) == Semantics.standalone(items, limit) : List<&2, Game.Tree>}:
  match fuel items:
    case 0n Nil{}:
      {==}
    case 1n+prior Nil{}:
      {==}
    case 0n head <> tail:
      match complete:
    case 1n++prior Semantics.State{0n, +board} <> tail:
      Lemmas.cons_cong(Game.Tree,
        Game.End{Chess.boundary(Chess.view(14n, board))}, Semantics.tree(limit, 0n, board),
        Semantics.forest(1n+prior, tail, limit, 14n), Semantics.standalone(tail, limit),
        canonical(1n+prior, limit, 0n, board, Unit{}),
        standalone(1n+prior, tail, limit, complete))
    case 1n++prior Semantics.State{1n+clock, +board} <> tail:
      (children, rest) = complete
      Lemmas.cons_cong(Game.Tree,
        Semantics.assemble(Graph.node(14n, Game.White{}, board),
          Semantics.forest(prior, Semantics.states(limit, 1n+clock,
            Semantics.children(Graph.node(14n, Game.White{}, board))), limit, 14n)),
        Semantics.tree(limit, 1n+clock, board),
        Semantics.forest(1n+prior, tail, limit, 14n), Semantics.standalone(tail, limit),
        canonical(1n+prior, limit, 1n+clock, board, (children, Unit{})),
        standalone(1n+prior, tail, limit, rest))

def unfold_complete(+fuel: Nat, +limit: Nat, +clock: Nat, +board: P.Position,
  complete: Semantics.NoCutoff(fuel, [Semantics.State{1n+clock, board}], limit, 14n)) ->
  {Choices.only(Semantics.forest(fuel, [Semantics.State{1n+clock, board}], limit, 14n)) ==
   Semantics.assemble(Graph.node(14n, Game.White{}, board),
     Semantics.standalone(Semantics.states(limit, 1n+clock,
       Semantics.children(Graph.node(14n, Game.White{}, board))), limit)) : Game.Tree}:
  match fuel:
    case 0n:
      match complete:
    case 1n++prior:
      (children, rest) = complete
      +node = Graph.node(14n, Game.White{}, board)
      +items = Semantics.states(limit, 1n+clock, Semantics.children(node))
      Equal.cong(List<&2, Game.Tree>, Game.Tree, trees => Semantics.assemble(node, trees),
        Semantics.forest(prior, items, limit, 14n), Semantics.standalone(items, limit),
        standalone(prior, items, limit, children))

# Unconditional one-step chess recurrence. Quiet children use clock-1;
# reset children use limit. Each destination has its own canonical budget.
def boundary(+limit: Nat, +board: P.Position) ->
  {Semantics.tree(limit, 0n, board) == Game.End{Chess.boundary(Chess.view(14n, board))} : Game.Tree}:
  Equal.sym(Game.Tree, Game.End{Chess.boundary(Chess.view(14n, board))}, Semantics.tree(limit, 0n, board),
    canonical(1n, limit, 0n, board, Unit{}))

def unfold(+limit: Nat, +clock: Nat, +board: P.Position) ->
  {Semantics.tree(limit, 1n+clock, board) ==
   Semantics.assemble(Graph.node(14n, Game.White{}, board),
     Semantics.standalone(Semantics.states(limit, 1n+clock,
       Semantics.children(Graph.node(14n, Game.White{}, board))), limit)) : Game.Tree}:
  unfold_complete(Measure.budget(limit, Measure.position(board), 1n+clock), limit, clock, board,
    Total.complete(limit, 1n+clock, 14n, board))

# Induction on an arbitrary legal line, not on positions or computed tables.
# This bounds repeated clock resets as well as quiet play.
def line_bound(+moves: List<&2, Chess.Action>, +limit: Nat, +remaining: Nat, +position: P.Position,
  line: Semantics.Line(moves, limit, remaining, position)) ->
  Measure.Le(List.length(&2, Chess.Action, moves), Measure.budget(limit, Measure.position(position), remaining)):
  match moves remaining:
    case Nil{} remaining:
      Unit{}
    case head <> tail 0n:
      match line:
    case head <> tail 1n+clock:
      (legal, continuation) = line
      MeasureProof.trans(1n+List.length(&2, Chess.Action, tail),
        1n+Measure.budget(limit, Measure.position(Chess.after(position, head)), Bool.pick(Nat, Chess.resets(position, head), limit, clock)),
        Measure.budget(limit, Measure.position(position), 1n+clock),
        line_bound(tail, limit, Bool.pick(Nat, Chess.resets(position, head), limit, clock), Chess.after(position, head), continuation),
        Selection.legal_budget(limit, clock, position, head, legal))
