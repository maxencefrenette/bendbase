import Base
import ./chess_game.bend as Semantics
import ./chess.bend as Chess
import ./chess_measure.bend as Measure
import ./chess_measure_proof.bend as MeasureProof
import ./chess_selection_proof.bend as Selection
import ./position.bend as P
import ./game.bend as Game

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
