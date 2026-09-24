import Base
import ./component_cache_proof.bend as StageProof
import ./component_cache.bend as Stages
import ./material_cache.bend as Registry
import ./table_cache_proof.bend as CacheProof
import ./table_cache.bend as Cache
import ./material_catalog.bend as Catalog
import ./dependency_engine.bend as Dependencies
import ./game.bend as Game
import ./pawnless_chess.bend as Chess
import ./pawn_chess.bend as Pawn
import ./pawnless_index.bend as Index
import ./pawnless_index_proof.bend as IndexProof
import ./finite_table.bend as Finite
import ./finite_table_proof.bend as FiniteProof
import ./pawnless_tables.bend as Pawnless
import ./pawnless_tables_proof.bend as PawnlessProof
import ./pawn_tables.bend as Tables
import ./table_engine_proof.bend as EngineProof
import ./pawn_component_proof.bend as ComponentProof

def position_square(+owner: Game.Player, +turn: Game.Player, +wk: Word(6n), +bk: Word(6n),
  +rank: Word(3n), +file: Word(3n)) ->
  {Pawn.position(Chess.Board{owner, turn, wk, bk, Pawn.square(rank, file)}) ==
   Pawn.Position{owner, turn, wk, bk, file} : Pawn.Position}:
  match rank:
    case WCon{a, WCon{b, WCon{c, WNil{}}}}:
      {==}

def position_board(+advance: Nat, +position: Pawn.Position) ->
  {Pawn.position(Pawn.board(advance, position)) == position : Pawn.Position}:
  match position:
    case Pawn.Position{owner, turn, wk, bk, file}:
      position_square(owner, turn, wk, bk, Pawn.rank(advance, owner), file)

def lookup_clock(+remaining: Nat, +advance: Nat, +position: Pawn.Position, +width: Nat, +size: {width == 20n : Nat},
  +lower: List<&2, Stages.Stage>, +promotions: List<&2, Registry.Named>) ->
  {Tables.lookup(width, advance, position, Tables.clock(remaining, advance, width, lower, promotions)) ==
   Tables.at(width, Tables.phase(remaining, advance, width, lower, promotions), position) : Game.Outcome}:
  %position_board(advance, position) :
    {Tables.lookup(width, advance, position, Tables.clock(remaining, advance, width, lower, promotions)) ==
     Tables.at(width, Tables.phase(remaining, advance, width, lower, promotions), _) : Game.Outcome}
  %IndexProof.roundtrip_at(width, size, Pawn.board(advance, position)) :
    {Tables.lookup(width, advance, position, Tables.clock(remaining, advance, width, lower, promotions)) ==
     Tables.at(width, Tables.phase(remaining, advance, width, lower, promotions), Pawn.position(_)) : Game.Outcome}
  ComponentProof.clock_get(remaining, advance, width, lower, promotions, Index.encode_at(width, Pawn.board(advance, position)))

def draws_get(depth: Nat, +key: Word(depth)) ->
  {Finite.get(depth, Game.Outcome, key, Tables.draws(depth)) == Game.Draw{} : Game.Outcome}:
  match depth key:
    case 0n WNil{}:
      {==}
    case 1n+rest WCon{False{}, tail}:
      draws_get(rest, tail)
    case 1n+rest WCon{True{}, tail}:
      draws_get(rest, tail)

def top_history(+advance: Nat, +width: Nat, +limit: Nat, +promotions: List<&2, Registry.Named>) ->
  {Tables.completed(advance, width, Tables.history(advance, width, limit, promotions)) ==
   Cache.Entry{width, Tables.solve(advance, limit, width, limit, promotions)} : Cache.Entry}:
  match advance:
    case 0n:
      {==}
    case 1n+prior:
      Equal.cong(Maybe<&2, Cache.Entry>, Cache.Entry,
        found => Dependencies.or_else(Cache.Entry, Cache.Entry{width, Tables.draws(width)}, found),
        Stages.select(Tables.history(advance, width, limit, promotions), advance, Catalog.pawn()),
        Some{Cache.Entry{width, Tables.solve(advance, limit, width, limit, promotions)}},
        StageProof.select_head(advance, Catalog.pawn(), Cache.Entry{width, Tables.solve(advance, limit, width, limit, promotions)},
          Tables.history(prior, width, limit, promotions)))

def completed_earlier(+advance: Nat, +width: Nat, +limit: Nat, +promotions: List<&2, Registry.Named>) ->
  {Tables.completed(advance, width, Tables.history(1n+advance, width, limit, promotions)) ==
   Tables.completed(advance, width, Tables.history(advance, width, limit, promotions)) : Cache.Entry}:
  Equal.cong(Maybe<&2, Cache.Entry>, Cache.Entry,
    found => Dependencies.or_else(Cache.Entry, Cache.Entry{width, Tables.draws(width)}, found),
    Stages.select(Tables.history(1n+advance, width, limit, promotions), advance, Catalog.pawn()),
    Stages.select(Tables.history(advance, width, limit, promotions), advance, Catalog.pawn()),
    StageProof.skip_next(advance,
      [Registry.Named{Catalog.pawn(), Cache.Entry{width, Tables.solve(1n+advance, limit, width, limit, promotions)}}],
      Tables.history(advance, width, limit, promotions), Catalog.pawn()))

def promoted_generated(+limit: Nat, +width: Nat, +material: Chess.Material) ->
  {Registry.find(Tables.promotions(limit, width), Catalog.signature(material)) ==
   Some{Cache.Entry{width, Pawnless.generate(limit, width, material)}} : Maybe<&2, Cache.Entry>}:
  match material:
    case Chess.Queen{}:
      {==}
    case Chess.Rook{}:
      {==}
    case Chess.Bishop{}:
      {==}
    case Chess.Knight{}:
      {==}

def sources(+advance: Nat, clock: Nat, +width: Nat, +limit: Nat) -> Tables.Sources<width>:
  +promotions = Tables.promotions(limit, width)
  +lower = Tables.history(advance, width, limit, promotions)
  Tables.Sources{Tables.solve(1n+advance, clock, width, limit, promotions),
    Tables.completed(advance, width, lower), Tables.completed(Stages.previous(advance), width, lower), promotions}

def lookup_base(+advance: Nat, +position: Pawn.Position, +width: Nat, +size: {width == 20n : Nat}, +limit: Nat) ->
  {Tables.lookup(width, 1n+advance, position, Tables.solve(1n+advance, 0n, width, limit, Tables.promotions(limit, width))) ==
   Game.evaluate(Pawn.boundary(Pawn.view(1n+advance, position))) : Game.Outcome}:
  lookup_clock(0n, 1n+advance, position, width, size,
    Tables.history(advance, width, limit, Tables.promotions(limit, width)), Tables.promotions(limit, width))

def lookup_step(+advance: Nat, +clock: Nat, +position: Pawn.Position, +width: Nat,
  +size: {width == 20n : Nat}, +limit: Nat) ->
  {Tables.lookup(width, 1n+advance, position, Tables.solve(1n+advance, 1n+clock, width, limit, Tables.promotions(limit, width))) ==
   Tables.combine(Pawn.view(1n+advance, position),
     Tables.values(Pawn.tasks(Pawn.view(1n+advance, position)), 1n+advance, width, sources(advance, clock, width, limit))) : Game.Outcome}:
  lookup_clock(1n+clock, 1n+advance, position, width, size,
    Tables.history(advance, width, limit, Tables.promotions(limit, width)), Tables.promotions(limit, width))

def assemble_evaluate(+view: Pawn.View, +trees: List<&2, Game.Tree>) ->
  {Tables.combine(view, PawnlessProof.outcomes(trees)) == Game.evaluate(Pawn.assemble(view, trees)) : Game.Outcome}:
  match view trees:
    case Pawn.Stop{outcome} _:
      {==}
    case Pawn.Play{turn, edges} Nil{}:
      {==}
    case Pawn.Play{+turn, edges} +head <> +tail:
      Equal.sym(Game.Outcome, Game.evaluate(Chess.choices(tail, turn, head)),
        Pawnless.fold(PawnlessProof.outcomes(tail), turn, Game.evaluate(head)),
        PawnlessProof.choices_evaluate(tail, turn, head))

# Symbolic observations of the memo tables, aligned with the two expansion
# stages of Pawn.forest. These are proof helpers, not another solver.
def forecast(+advance: Nat, +remaining: Nat, +stage: Nat, items: List<&2, Pawn.Task>, +width: Nat, +limit: Nat) -> List<&2, Game.Outcome>:
  match advance remaining stage items:
    case _ _ _ Nil{}:
      Nil{}
    case 1n++prior _ 1n Pawn.Here{position} <> tail:
      Tables.lookup(width, 1n+prior, position, Tables.solve(1n+prior, remaining, width, limit, Tables.promotions(limit, width))) <>
        forecast(1n+prior, remaining, 1n, tail, width, limit)
    case 1n++prior 1n++clock 0n Pawn.Follow{edge} <> tail:
      Tables.edge_value(1n+prior, edge, width, sources(prior, clock, width, limit)) <>
        forecast(1n+prior, 1n+clock, 0n, tail, width, limit)
    case _ _ _ head <> tail:
      Game.Draw{} <> forecast(advance, remaining, stage, tail, width, limit)

def forecast_edges(+advance: Nat, +clock: Nat, +items: List<&2, Pawn.Task>, +width: Nat, +limit: Nat) ->
  {Tables.values(items, 1n+advance, width, sources(advance, clock, width, limit)) ==
   forecast(1n+advance, 1n+clock, 0n, items, width, limit) : List<&2, Game.Outcome>}:
  match items:
    case Nil{}:
      {==}
    case Pawn.Follow{+edge} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome,
        Tables.edge_value(1n+advance, edge, width, sources(advance, clock, width, limit)),
        Tables.edge_value(1n+advance, edge, width, sources(advance, clock, width, limit)),
        Tables.values(tail, 1n+advance, width, sources(advance, clock, width, limit)),
        forecast(1n+advance, 1n+clock, 0n, tail, width, limit), {==}, forecast_edges(advance, clock, tail, width, limit))
    case Pawn.Here{position} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        Tables.values(tail, 1n+advance, width, sources(advance, clock, width, limit)),
        forecast(1n+advance, 1n+clock, 0n, tail, width, limit), {==}, forecast_edges(advance, clock, tail, width, limit))

def forecast_here(+advance: Nat, +clock: Nat, +position: Pawn.Position, +width: Nat, +limit: Nat) ->
  {Tables.lookup(width, advance, position, Tables.solve(advance, clock, width, limit, Tables.promotions(limit, width))) ==
   PawnlessProof.first(forecast(advance, clock, 1n, Pawn.Here{position} <> Nil{}, width, limit)) : Game.Outcome}:
  match advance clock:
    case 0n _:
      draws_get(width, Index.encode_at(width, Pawn.board(0n, position)))
    case 1n+prior 0n:
      {==}
    case 1n+prior 1n+rest:
      {==}

def here_from_forest(+advance: Nat, +clock: Nat, +position: Pawn.Position, +width: Nat, +limit: Nat,
  correct: {forecast(advance, clock, 1n, Pawn.Here{position} <> Nil{}, width, limit) ==
    PawnlessProof.outcomes(Pawn.forest(advance, clock, 1n, Pawn.Here{position} <> Nil{}, limit)) : List<&2, Game.Outcome>}) ->
  {Tables.lookup(width, advance, position, Tables.solve(advance, clock, width, limit, Tables.promotions(limit, width))) ==
   Game.evaluate(Chess.only(Pawn.forest(advance, clock, 1n, Pawn.Here{position} <> Nil{}, limit))) : Game.Outcome}:
  +items = {Pawn.Here{position} <> Nil{} : List<&2, Pawn.Task>}
  +trees = Pawn.forest(advance, clock, 1n, items, limit)
  Equal.trans(Game.Outcome,
    Tables.lookup(width, advance, position, Tables.solve(advance, clock, width, limit, Tables.promotions(limit, width))),
    PawnlessProof.first(forecast(advance, clock, 1n, items, width, limit)), Game.evaluate(Chess.only(trees)),
    forecast_here(advance, clock, position, width, limit),
    Equal.trans(Game.Outcome,
      PawnlessProof.first(forecast(advance, clock, 1n, items, width, limit)),
      PawnlessProof.first(PawnlessProof.outcomes(trees)), Game.evaluate(Chess.only(trees)),
      Equal.cong(List<&2, Game.Outcome>, Game.Outcome, values => PawnlessProof.first(values),
        forecast(advance, clock, 1n, items, width, limit), PawnlessProof.outcomes(trees), correct),
      PawnlessProof.first_outcomes(trees)))

def push_from_here(+advance: Nat, +clock: Nat, +position: Pawn.Position, +width: Nat, +limit: Nat,
  correct: {Tables.lookup(width, advance, position, Tables.solve(advance, limit, width, limit, Tables.promotions(limit, width))) ==
    Game.evaluate(Chess.only(Pawn.forest(advance, limit, 1n, Pawn.Here{position} <> Nil{}, limit))) : Game.Outcome}) ->
  {Tables.edge_value(1n+advance, Pawn.Push{position}, width, sources(advance, clock, width, limit)) ==
   Game.evaluate(Chess.only(Pawn.forest(advance, limit, 1n, Pawn.Here{position} <> Nil{}, limit))) : Game.Outcome}:
  %Equal.sym(Cache.Entry,
    Tables.completed(advance, width, Tables.history(advance, width, limit, Tables.promotions(limit, width))),
    Cache.Entry{width, Tables.solve(advance, limit, width, limit, Tables.promotions(limit, width))},
    top_history(advance, width, limit, Tables.promotions(limit, width))) :
    {Tables.dependency(width, advance, position, _) ==
     Game.evaluate(Chess.only(Pawn.forest(advance, limit, 1n, Pawn.Here{position} <> Nil{}, limit))) : Game.Outcome}
  Equal.trans(Game.Outcome,
    Tables.dependency(width, advance, position, Cache.Entry{width, Tables.solve(advance, limit, width, limit, Tables.promotions(limit, width))}),
    Tables.lookup(width, advance, position, Tables.solve(advance, limit, width, limit, Tables.promotions(limit, width))),
    Game.evaluate(Chess.only(Pawn.forest(advance, limit, 1n, Pawn.Here{position} <> Nil{}, limit))),
    CacheProof.fallback_unused(width, Index.encode_at(width, Pawn.board(advance, position)),
      Tables.solve(advance, limit, width, limit, Tables.promotions(limit, width)), Game.Draw{}), correct)

def double_from_here(+advance: Nat, +clock: Nat, +position: Pawn.Position, +width: Nat, +limit: Nat,
  correct: {Tables.lookup(width, advance, position, Tables.solve(advance, limit, width, limit, Tables.promotions(limit, width))) ==
    Game.evaluate(Chess.only(Pawn.forest(advance, limit, 1n, Pawn.Here{position} <> Nil{}, limit))) : Game.Outcome}) ->
  {Tables.edge_value(1n+1n+advance, Pawn.DoublePush{position}, width, sources(1n+advance, clock, width, limit)) ==
   Game.evaluate(Chess.only(Pawn.forest(advance, limit, 1n, Pawn.Here{position} <> Nil{}, limit))) : Game.Outcome}:
  %Equal.sym(Cache.Entry,
    Tables.completed(advance, width, Tables.history(1n+advance, width, limit, Tables.promotions(limit, width))),
    Tables.completed(advance, width, Tables.history(advance, width, limit, Tables.promotions(limit, width))),
    completed_earlier(advance, width, limit, Tables.promotions(limit, width))) :
    {Tables.dependency(width, advance, position, _) ==
     Game.evaluate(Chess.only(Pawn.forest(advance, limit, 1n, Pawn.Here{position} <> Nil{}, limit))) : Game.Outcome}
  push_from_here(advance, clock, position, width, limit, correct)

def promotion_correct(+advance: Nat, +clock: Nat, +material: Chess.Material, +board: Chess.Board,
  +width: Nat, +size: {width == 20n : Nat}, +limit: Nat) ->
  {Tables.edge_value(1n+advance, Pawn.Promoted{material, board}, width, sources(advance, clock, width, limit)) ==
   Game.evaluate(Chess.tree(limit, material, board)) : Game.Outcome}:
  %Equal.sym(Maybe<&2, Cache.Entry>,
    Registry.find(Tables.promotions(limit, width), Catalog.signature(material)),
    Some{Cache.Entry{width, Pawnless.generate(limit, width, material)}}, promoted_generated(limit, width, material)) :
    {Cache.value(Registry.read(width, Index.encode_at(width, board), _), Game.Draw{}) ==
     Game.evaluate(Chess.tree(limit, material, board)) : Game.Outcome}
  Equal.trans(Game.Outcome,
    Cache.value(Cache.lookup(width, Index.encode_at(width, board), Cache.Entry{width, Pawnless.generate(limit, width, material)}), Game.Draw{}),
    Finite.get(width, Game.Outcome, Index.encode_at(width, board), Pawnless.generate(limit, width, material)),
    Game.evaluate(Chess.tree(limit, material, board)),
    CacheProof.fallback_unused(width, Index.encode_at(width, board), Pawnless.generate(limit, width, material), Game.Draw{}),
    PawnlessProof.pointwise(limit, width, size, material, board))

def step_from_children(+advance: Nat, +clock: Nat, +position: Pawn.Position,
  +width: Nat, +size: {width == 20n : Nat}, +limit: Nat,
  correct: {forecast(1n+advance, 1n+clock, 0n, Pawn.tasks(Pawn.view(1n+advance, position)), width, limit) ==
    PawnlessProof.outcomes(Pawn.forest(1n+advance, 1n+clock, 0n, Pawn.tasks(Pawn.view(1n+advance, position)), limit)) : List<&2, Game.Outcome>}) ->
  {Tables.lookup(width, 1n+advance, position, Tables.solve(1n+advance, 1n+clock, width, limit, Tables.promotions(limit, width))) ==
   Game.evaluate(Pawn.assemble(Pawn.view(1n+advance, position),
     Pawn.forest(1n+advance, 1n+clock, 0n, Pawn.tasks(Pawn.view(1n+advance, position)), limit))) : Game.Outcome}:
  +node = Pawn.view(1n+advance, position)
  +prior = Tables.values(Pawn.tasks(node), 1n+advance, width, sources(advance, clock, width, limit))
  +trees = Pawn.forest(1n+advance, 1n+clock, 0n, Pawn.tasks(node), limit)
  Equal.trans(Game.Outcome,
    Tables.lookup(width, 1n+advance, position, Tables.solve(1n+advance, 1n+clock, width, limit, Tables.promotions(limit, width))),
    Tables.combine(node, prior), Game.evaluate(Pawn.assemble(node, trees)),
    lookup_step(advance, clock, position, width, size, limit),
    Equal.trans(Game.Outcome, Tables.combine(node, prior), Tables.combine(node, PawnlessProof.outcomes(trees)),
      Game.evaluate(Pawn.assemble(node, trees)),
      Equal.cong(List<&2, Game.Outcome>, Game.Outcome, values => Tables.combine(node, values),
        prior, PawnlessProof.outcomes(trees),
        Equal.trans(List<&2, Game.Outcome>, prior,
          forecast(1n+advance, 1n+clock, 0n, Pawn.tasks(node), width, limit), PawnlessProof.outcomes(trees),
          forecast_edges(advance, clock, Pawn.tasks(node), width, limit), correct)), assemble_evaluate(node, trees)))

# Lexicographic induction, not enumeration: every board, move list, clock and
# pawn distance remains universally quantified.
def forest_correct(+advance: Nat, +remaining: Nat, +stage: Nat, +items: List<&2, Pawn.Task>,
  +width: Nat, +size: {width == 20n : Nat}, +limit: Nat) ->
  {forecast(advance, remaining, stage, items, width, limit) ==
   PawnlessProof.outcomes(Pawn.forest(advance, remaining, stage, items, limit)) : List<&2, Game.Outcome>}:
  match advance remaining stage items:
    case 0n _ _ Nil{}:
      {==}
    case 1n 0n 0n Nil{}:
      {==}
    case 1n+1n+prior 0n 0n Nil{}:
      {==}
    case 1n 0n 1n Nil{}:
      {==}
    case 1n+1n+prior 0n 1n Nil{}:
      {==}
    case 1n 1n+clock 0n Nil{}:
      {==}
    case 1n+1n+prior 1n+clock 0n Nil{}:
      {==}
    case 1n 1n+clock 1n Nil{}:
      {==}
    case 1n+1n+prior 1n+clock 1n Nil{}:
      {==}
    case 1n 0n 1n+1n+extra Nil{}:
      {==}
    case 1n+1n+prior 0n 1n+1n+extra Nil{}:
      {==}
    case 1n 1n+clock 1n+1n+extra Nil{}:
      {==}
    case 1n+1n+prior 1n+clock 1n+1n+extra Nil{}:
      {==}
    case 1n 0n 1n Pawn.Here{+position} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome,
        Tables.lookup(width, 1n+0n, position, Tables.solve(1n+0n, 0n, width, limit, Tables.promotions(limit, width))), Game.evaluate(Pawn.boundary(Pawn.view(1n+0n, position))),
        forecast(1n+0n, 0n, 1n, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+0n, 0n, 1n, tail, limit)),
        lookup_base(0n, position, width, size, limit), forest_correct(1n+0n, 0n, 1n, tail, width, size, limit))
    case 1n+1n++prior 0n 1n Pawn.Here{+position} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome,
        Tables.lookup(width, 1n+1n+prior, position, Tables.solve(1n+1n+prior, 0n, width, limit, Tables.promotions(limit, width))), Game.evaluate(Pawn.boundary(Pawn.view(1n+1n+prior, position))),
        forecast(1n+1n+prior, 0n, 1n, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+1n+prior, 0n, 1n, tail, limit)),
        lookup_base(1n+prior, position, width, size, limit), forest_correct(1n+1n+prior, 0n, 1n, tail, width, size, limit))
    case 1n 1n++clock 1n Pawn.Here{+position} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome,
        Tables.lookup(width, 1n+0n, position, Tables.solve(1n+0n, 1n+clock, width, limit, Tables.promotions(limit, width))), Game.evaluate(Pawn.assemble(Pawn.view(1n+0n, position), Pawn.forest(1n+0n, 1n+clock, 0n, Pawn.tasks(Pawn.view(1n+0n, position)), limit))),
        forecast(1n+0n, 1n+clock, 1n, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+0n, 1n+clock, 1n, tail, limit)),
        step_from_children(0n, clock, position, width, size, limit,
          forest_correct(1n+0n, 1n+clock, 0n, Pawn.tasks(Pawn.view(1n+0n, position)), width, size, limit)), forest_correct(1n+0n, 1n+clock, 1n, tail, width, size, limit))
    case 1n+1n++prior 1n++clock 1n Pawn.Here{+position} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome,
        Tables.lookup(width, 1n+1n+prior, position, Tables.solve(1n+1n+prior, 1n+clock, width, limit, Tables.promotions(limit, width))), Game.evaluate(Pawn.assemble(Pawn.view(1n+1n+prior, position), Pawn.forest(1n+1n+prior, 1n+clock, 0n, Pawn.tasks(Pawn.view(1n+1n+prior, position)), limit))),
        forecast(1n+1n+prior, 1n+clock, 1n, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+1n+prior, 1n+clock, 1n, tail, limit)),
        step_from_children(1n+prior, clock, position, width, size, limit,
          forest_correct(1n+1n+prior, 1n+clock, 0n, Pawn.tasks(Pawn.view(1n+1n+prior, position)), width, size, limit)), forest_correct(1n+1n+prior, 1n+clock, 1n, tail, width, size, limit))
    case 1n 1n++clock 0n Pawn.Follow{Pawn.Quiet{+position}} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome,
        Tables.edge_value(1n+0n, Pawn.Quiet{position}, width, sources(0n, clock, width, limit)), Game.evaluate(Chess.only(Pawn.forest(1n+0n, clock, 1n, Pawn.Here{position} <> Nil{}, limit))),
        forecast(1n+0n, 1n+clock, 0n, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+0n, 1n+clock, 0n, tail, limit)),
        here_from_forest(1n+0n, clock, position, width, limit,
          forest_correct(1n+0n, clock, 1n, Pawn.Here{position} <> Nil{}, width, size, limit)), forest_correct(1n+0n, 1n+clock, 0n, tail, width, size, limit))
    case 1n+1n++prior 1n++clock 0n Pawn.Follow{Pawn.Quiet{+position}} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome,
        Tables.edge_value(1n+1n+prior, Pawn.Quiet{position}, width, sources(1n+prior, clock, width, limit)), Game.evaluate(Chess.only(Pawn.forest(1n+1n+prior, clock, 1n, Pawn.Here{position} <> Nil{}, limit))),
        forecast(1n+1n+prior, 1n+clock, 0n, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+1n+prior, 1n+clock, 0n, tail, limit)),
        here_from_forest(1n+1n+prior, clock, position, width, limit,
          forest_correct(1n+1n+prior, clock, 1n, Pawn.Here{position} <> Nil{}, width, size, limit)), forest_correct(1n+1n+prior, 1n+clock, 0n, tail, width, size, limit))
    case 1n 1n++clock 0n Pawn.Follow{Pawn.Push{+position}} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome,
        Tables.edge_value(1n+0n, Pawn.Push{position}, width, sources(0n, clock, width, limit)), Game.evaluate(Chess.only(Pawn.forest(0n, limit, 1n, Pawn.Here{position} <> Nil{}, limit))),
        forecast(1n+0n, 1n+clock, 0n, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+0n, 1n+clock, 0n, tail, limit)),
        push_from_here(0n, clock, position, width, limit, here_from_forest(0n, limit, position, width, limit,
          forest_correct(0n, limit, 1n, Pawn.Here{position} <> Nil{}, width, size, limit))), forest_correct(1n+0n, 1n+clock, 0n, tail, width, size, limit))
    case 1n+1n++prior 1n++clock 0n Pawn.Follow{Pawn.Push{+position}} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome,
        Tables.edge_value(1n+1n+prior, Pawn.Push{position}, width, sources(1n+prior, clock, width, limit)), Game.evaluate(Chess.only(Pawn.forest(1n+prior, limit, 1n, Pawn.Here{position} <> Nil{}, limit))),
        forecast(1n+1n+prior, 1n+clock, 0n, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+1n+prior, 1n+clock, 0n, tail, limit)),
        push_from_here(1n+prior, clock, position, width, limit, here_from_forest(1n+prior, limit, position, width, limit,
          forest_correct(1n+prior, limit, 1n, Pawn.Here{position} <> Nil{}, width, size, limit))), forest_correct(1n+1n+prior, 1n+clock, 0n, tail, width, size, limit))
    case 1n+1n++prior 1n++clock 0n Pawn.Follow{Pawn.DoublePush{+position}} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome,
        Tables.edge_value(1n+1n+prior, Pawn.DoublePush{position}, width, sources(1n+prior, clock, width, limit)), Game.evaluate(Chess.only(Pawn.forest(prior, limit, 1n, Pawn.Here{position} <> Nil{}, limit))),
        forecast(1n+1n+prior, 1n+clock, 0n, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+1n+prior, 1n+clock, 0n, tail, limit)),
        double_from_here(prior, clock, position, width, limit, here_from_forest(prior, limit, position, width, limit,
          forest_correct(prior, limit, 1n, Pawn.Here{position} <> Nil{}, width, size, limit))), forest_correct(1n+1n+prior, 1n+clock, 0n, tail, width, size, limit))
    case 1n 1n++clock 0n Pawn.Follow{Pawn.Promoted{+material, +board}} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome,
        Tables.edge_value(1n+0n, Pawn.Promoted{material, board}, width, sources(0n, clock, width, limit)), Game.evaluate(Chess.tree(limit, material, board)),
        forecast(1n+0n, 1n+clock, 0n, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+0n, 1n+clock, 0n, tail, limit)),
        promotion_correct(0n, clock, material, board, width, size, limit), forest_correct(1n+0n, 1n+clock, 0n, tail, width, size, limit))
    case 1n+1n++prior 1n++clock 0n Pawn.Follow{Pawn.Promoted{+material, +board}} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome,
        Tables.edge_value(1n+1n+prior, Pawn.Promoted{material, board}, width, sources(1n+prior, clock, width, limit)), Game.evaluate(Chess.tree(limit, material, board)),
        forecast(1n+1n+prior, 1n+clock, 0n, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+1n+prior, 1n+clock, 0n, tail, limit)),
        promotion_correct(1n+prior, clock, material, board, width, size, limit), forest_correct(1n+1n+prior, 1n+clock, 0n, tail, width, size, limit))
    case 0n _ _ head <> +tail:
      PawnlessProof.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        forecast(0n, remaining, stage, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(0n, remaining, stage, tail, limit)),
        {==}, forest_correct(0n, remaining, stage, tail, width, size, limit))
    case 1n 0n 1n+1n++extra head <> +tail:
      PawnlessProof.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        forecast(1n+0n, 0n, 1n+1n+extra, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+0n, 0n, 1n+1n+extra, tail, limit)),
        {==}, forest_correct(1n+0n, 0n, 1n+1n+extra, tail, width, size, limit))
    case 1n+1n++prior 0n 1n+1n++extra head <> +tail:
      PawnlessProof.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        forecast(1n+1n+prior, 0n, 1n+1n+extra, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+1n+prior, 0n, 1n+1n+extra, tail, limit)),
        {==}, forest_correct(1n+1n+prior, 0n, 1n+1n+extra, tail, width, size, limit))
    case 1n 1n++clock 1n+1n++extra head <> +tail:
      PawnlessProof.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        forecast(1n+0n, 1n+clock, 1n+1n+extra, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+0n, 1n+clock, 1n+1n+extra, tail, limit)),
        {==}, forest_correct(1n+0n, 1n+clock, 1n+1n+extra, tail, width, size, limit))
    case 1n+1n++prior 1n++clock 1n+1n++extra head <> +tail:
      PawnlessProof.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        forecast(1n+1n+prior, 1n+clock, 1n+1n+extra, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+1n+prior, 1n+clock, 1n+1n+extra, tail, limit)),
        {==}, forest_correct(1n+1n+prior, 1n+clock, 1n+1n+extra, tail, width, size, limit))
    case 1n 0n 0n Pawn.Here{position} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        forecast(1n+0n, 0n, 0n, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+0n, 0n, 0n, tail, limit)),
        {==}, forest_correct(1n+0n, 0n, 0n, tail, width, size, limit))
    case 1n+1n++prior 0n 0n Pawn.Here{position} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        forecast(1n+1n+prior, 0n, 0n, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+1n+prior, 0n, 0n, tail, limit)),
        {==}, forest_correct(1n+1n+prior, 0n, 0n, tail, width, size, limit))
    case 1n 1n++clock 0n Pawn.Here{position} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        forecast(1n+0n, 1n+clock, 0n, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+0n, 1n+clock, 0n, tail, limit)),
        {==}, forest_correct(1n+0n, 1n+clock, 0n, tail, width, size, limit))
    case 1n+1n++prior 1n++clock 0n Pawn.Here{position} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        forecast(1n+1n+prior, 1n+clock, 0n, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+1n+prior, 1n+clock, 0n, tail, limit)),
        {==}, forest_correct(1n+1n+prior, 1n+clock, 0n, tail, width, size, limit))
    case 1n 0n 1n Pawn.Follow{edge} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        forecast(1n+0n, 0n, 1n, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+0n, 0n, 1n, tail, limit)),
        {==}, forest_correct(1n+0n, 0n, 1n, tail, width, size, limit))
    case 1n+1n++prior 0n 1n Pawn.Follow{edge} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        forecast(1n+1n+prior, 0n, 1n, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+1n+prior, 0n, 1n, tail, limit)),
        {==}, forest_correct(1n+1n+prior, 0n, 1n, tail, width, size, limit))
    case 1n 1n++clock 1n Pawn.Follow{edge} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        forecast(1n+0n, 1n+clock, 1n, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+0n, 1n+clock, 1n, tail, limit)),
        {==}, forest_correct(1n+0n, 1n+clock, 1n, tail, width, size, limit))
    case 1n+1n++prior 1n++clock 1n Pawn.Follow{edge} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        forecast(1n+1n+prior, 1n+clock, 1n, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+1n+prior, 1n+clock, 1n, tail, limit)),
        {==}, forest_correct(1n+1n+prior, 1n+clock, 1n, tail, width, size, limit))
    case 1n 0n 0n Pawn.Follow{edge} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        forecast(1n+0n, 0n, 0n, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+0n, 0n, 0n, tail, limit)),
        {==}, forest_correct(1n+0n, 0n, 0n, tail, width, size, limit))
    case 1n+1n++prior 0n 0n Pawn.Follow{edge} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        forecast(1n+1n+prior, 0n, 0n, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+1n+prior, 0n, 0n, tail, limit)),
        {==}, forest_correct(1n+1n+prior, 0n, 0n, tail, width, size, limit))
    case 1n 1n++clock 0n Pawn.Follow{Pawn.Captured{}} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        forecast(1n+0n, 1n+clock, 0n, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+0n, 1n+clock, 0n, tail, limit)),
        {==}, forest_correct(1n+0n, 1n+clock, 0n, tail, width, size, limit))
    case 1n+1n++prior 1n++clock 0n Pawn.Follow{Pawn.Captured{}} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        forecast(1n+1n+prior, 1n+clock, 0n, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n+1n+prior, 1n+clock, 0n, tail, limit)),
        {==}, forest_correct(1n+1n+prior, 1n+clock, 0n, tail, width, size, limit))
    case 1n 1n++clock 0n Pawn.Follow{Pawn.DoublePush{position}} <> +tail:
      PawnlessProof.cons_cong(Game.Outcome, Game.Draw{}, Game.Draw{},
        forecast(1n, 1n+clock, 0n, tail, width, limit),
        PawnlessProof.outcomes(Pawn.forest(1n, 1n+clock, 0n, tail, limit)),
        {==}, forest_correct(1n, 1n+clock, 0n, tail, width, size, limit))

def clock_position(+advance: Nat, +remaining: Nat, +board: Chess.Board, +width: Nat, +size: {width == 20n : Nat},
  +lower: List<&2, Stages.Stage>, +promotions: List<&2, Registry.Named>) ->
  {Finite.get(width, Game.Outcome, Index.encode_at(width, board), Tables.clock(remaining, advance, width, lower, promotions)) ==
   Tables.lookup(width, advance, Pawn.position(board), Tables.clock(remaining, advance, width, lower, promotions)) : Game.Outcome}:
  +position = Pawn.position(board)
  +table = Tables.clock(remaining, advance, width, lower, promotions)
  +step = Tables.phase(remaining, advance, width, lower, promotions)
  Equal.trans(Game.Outcome,
    Finite.get(width, Game.Outcome, Index.encode_at(width, board), table),
    Tables.at(width, step, position), Tables.lookup(width, advance, position, table),
    Equal.trans(Game.Outcome,
      Finite.get(width, Game.Outcome, Index.encode_at(width, board), table),
      Tables.at(width, step, Pawn.position(Index.decode_at(width, Index.encode_at(width, board)))),
      Tables.at(width, step, position),
      ComponentProof.clock_get(remaining, advance, width, lower, promotions, Index.encode_at(width, board)),
      Equal.cong(Chess.Board, Game.Outcome, input => Tables.at(width, step, Pawn.position(input)),
        Index.decode_at(width, Index.encode_at(width, board)), board, IndexProof.roundtrip_at(width, size, board))),
    Equal.sym(Game.Outcome, Tables.lookup(width, advance, position, table), Tables.at(width, step, position),
      lookup_clock(remaining, advance, position, width, size, lower, promotions)))

def solve_position(+advance: Nat, +remaining: Nat, +board: Chess.Board,
  +width: Nat, +size: {width == 20n : Nat}, +limit: Nat) ->
  {Finite.get(width, Game.Outcome, Index.encode_at(width, board), Tables.solve(advance, remaining, width, limit, Tables.promotions(limit, width))) ==
   Tables.lookup(width, advance, Pawn.position(board), Tables.solve(advance, remaining, width, limit, Tables.promotions(limit, width))) : Game.Outcome}:
  match advance remaining:
    case 0n _:
      Equal.trans(Game.Outcome,
        Finite.get(width, Game.Outcome, Index.encode_at(width, board), Tables.draws(width)), Game.Draw{},
        Tables.lookup(width, 0n, Pawn.position(board), Tables.draws(width)),
        draws_get(width, Index.encode_at(width, board)),
        Equal.sym(Game.Outcome, Tables.lookup(width, 0n, Pawn.position(board), Tables.draws(width)), Game.Draw{},
          draws_get(width, Index.encode_at(width, Pawn.board(0n, Pawn.position(board))))))
    case 1n+prior 0n:
      clock_position(1n+prior, 0n, board, width, size,
        Tables.history(prior, width, limit, Tables.promotions(limit, width)), Tables.promotions(limit, width))
    case 1n+prior 1n+clock:
      clock_position(1n+prior, 1n+clock, board, width, size,
        Tables.history(prior, width, limit, Tables.promotions(limit, width)), Tables.promotions(limit, width))

def solved_board(+limit: Nat, +width: Nat, +size: {width == 20n : Nat}, +board: Chess.Board) ->
  {Finite.get(width, Game.Outcome, Index.encode_at(width, board),
     Tables.solve(Pawn.advance(board), limit, width, limit, Tables.promotions(limit, width))) ==
   Game.evaluate(Pawn.tree(limit, board)) : Game.Outcome}:
  +advance = Pawn.advance(board)
  +position = Pawn.position(board)
  Equal.trans(Game.Outcome,
    Finite.get(width, Game.Outcome, Index.encode_at(width, board), Tables.solve(advance, limit, width, limit, Tables.promotions(limit, width))),
    Tables.lookup(width, advance, position, Tables.solve(advance, limit, width, limit, Tables.promotions(limit, width))),
    Game.evaluate(Pawn.tree(limit, board)),
    solve_position(advance, limit, board, width, size, limit),
    here_from_forest(advance, limit, position, width, limit,
      forest_correct(advance, limit, 1n, Pawn.Here{position} <> Nil{}, width, size, limit)))

def finish_get(depth: Nat, +width: Nat, +ranks: List<&2, Stages.Stage>,
  +keys: Finite.Table(depth, Word(width)), +key: Word(depth)) ->
  {Finite.get(depth, Game.Outcome, key, Tables.finish(depth, width, ranks, keys)) ==
   Tables.stored(Pawn.advance(Index.decode_at(width, Finite.get(depth, Word(width), key, keys))), width, ranks,
     Finite.get(depth, Word(width), key, keys)) : Game.Outcome}:
  EngineProof.fill_get(~Tables.RankContext, ~Tables.stored_entry, depth, width, 0n, ranks, keys, key)

def finish_lookup(+width: Nat, +ranks: List<&2, Stages.Stage>, +key: Word(width)) ->
  {Finite.get(width, Game.Outcome, key, Tables.finish(width, width, ranks, Finite.keys(width))) ==
   Tables.stored(Pawn.advance(Index.decode_at(width, key)), width, ranks, key) : Game.Outcome}:
  %FiniteProof.keys_get(width, key) :
    {Finite.get(width, Game.Outcome, key, Tables.finish(width, width, ranks, Finite.keys(width))) ==
     Tables.stored(Pawn.advance(Index.decode_at(width, _)), width, ranks, _) : Game.Outcome}
  finish_get(width, width, ranks, Finite.keys(width), key)

# The only finite case split here is over the pawn's rank and color (16
# combinations), not over positions. The kings, file and turn stay symbolic.
def stored_rank(+owner: Game.Player, +rank: Word(3n), +width: Nat, +limit: Nat, +key: Word(width)) ->
  {Tables.stored(Pawn.distance(owner, rank), width, Tables.history(6n, width, limit, Tables.promotions(limit, width)), key) ==
   Finite.get(width, Game.Outcome, key,
     Tables.solve(Pawn.distance(owner, rank), limit, width, limit, Tables.promotions(limit, width))) : Game.Outcome}:
  match owner rank:
    case Game.White{} WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}:
      Equal.sym(Game.Outcome, Finite.get(width, Game.Outcome, key, Tables.draws(width)), Game.Draw{}, draws_get(width, key))
    case Game.White{} WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}:
      CacheProof.fallback_unused(width, key,
        Tables.solve(Pawn.distance(owner, rank), limit, width, limit, Tables.promotions(limit, width)), Game.Draw{})
    case Game.White{} WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}:
      CacheProof.fallback_unused(width, key,
        Tables.solve(Pawn.distance(owner, rank), limit, width, limit, Tables.promotions(limit, width)), Game.Draw{})
    case Game.White{} WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}:
      CacheProof.fallback_unused(width, key,
        Tables.solve(Pawn.distance(owner, rank), limit, width, limit, Tables.promotions(limit, width)), Game.Draw{})
    case Game.White{} WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}:
      CacheProof.fallback_unused(width, key,
        Tables.solve(Pawn.distance(owner, rank), limit, width, limit, Tables.promotions(limit, width)), Game.Draw{})
    case Game.White{} WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}:
      CacheProof.fallback_unused(width, key,
        Tables.solve(Pawn.distance(owner, rank), limit, width, limit, Tables.promotions(limit, width)), Game.Draw{})
    case Game.White{} WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}:
      CacheProof.fallback_unused(width, key,
        Tables.solve(Pawn.distance(owner, rank), limit, width, limit, Tables.promotions(limit, width)), Game.Draw{})
    case Game.White{} WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}:
      Equal.sym(Game.Outcome, Finite.get(width, Game.Outcome, key, Tables.draws(width)), Game.Draw{}, draws_get(width, key))
    case Game.Black{} WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}:
      Equal.sym(Game.Outcome, Finite.get(width, Game.Outcome, key, Tables.draws(width)), Game.Draw{}, draws_get(width, key))
    case Game.Black{} WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}:
      CacheProof.fallback_unused(width, key,
        Tables.solve(Pawn.distance(owner, rank), limit, width, limit, Tables.promotions(limit, width)), Game.Draw{})
    case Game.Black{} WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}:
      CacheProof.fallback_unused(width, key,
        Tables.solve(Pawn.distance(owner, rank), limit, width, limit, Tables.promotions(limit, width)), Game.Draw{})
    case Game.Black{} WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}:
      CacheProof.fallback_unused(width, key,
        Tables.solve(Pawn.distance(owner, rank), limit, width, limit, Tables.promotions(limit, width)), Game.Draw{})
    case Game.Black{} WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}:
      CacheProof.fallback_unused(width, key,
        Tables.solve(Pawn.distance(owner, rank), limit, width, limit, Tables.promotions(limit, width)), Game.Draw{})
    case Game.Black{} WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}:
      CacheProof.fallback_unused(width, key,
        Tables.solve(Pawn.distance(owner, rank), limit, width, limit, Tables.promotions(limit, width)), Game.Draw{})
    case Game.Black{} WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}:
      CacheProof.fallback_unused(width, key,
        Tables.solve(Pawn.distance(owner, rank), limit, width, limit, Tables.promotions(limit, width)), Game.Draw{})
    case Game.Black{} WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}:
      Equal.sym(Game.Outcome, Finite.get(width, Game.Outcome, key, Tables.draws(width)), Game.Draw{}, draws_get(width, key))

def stored_board(+board: Chess.Board, +width: Nat, +limit: Nat, +key: Word(width)) ->
  {Tables.stored(Pawn.advance(board), width, Tables.history(6n, width, limit, Tables.promotions(limit, width)), key) ==
   Finite.get(width, Game.Outcome, key,
     Tables.solve(Pawn.advance(board), limit, width, limit, Tables.promotions(limit, width))) : Game.Outcome}:
  match board:
    case Chess.Board{owner, turn, wk, bk, WCon{a, WCon{b, WCon{c, file}}}}:
      stored_rank(owner, WCon{a, WCon{b, WCon{c, WNil{}}}}, width, limit, key)

def pointwise(+limit: Nat, +width: Nat, +size: {width == 20n : Nat}, +board: Chess.Board) ->
  {Finite.get(width, Game.Outcome, Index.encode_at(width, board), Tables.generate(limit, width)) ==
   Game.evaluate(Pawn.tree(limit, board)) : Game.Outcome}:
  +key = Index.encode_at(width, board)
  +ranks = Tables.history(6n, width, limit, Tables.promotions(limit, width))
  Equal.trans(Game.Outcome,
    Finite.get(width, Game.Outcome, key, Tables.generate(limit, width)),
    Tables.stored(Pawn.advance(Index.decode_at(width, key)), width, ranks, key),
    Game.evaluate(Pawn.tree(limit, board)), finish_lookup(width, ranks, key),
    Equal.trans(Game.Outcome,
      Tables.stored(Pawn.advance(Index.decode_at(width, key)), width, ranks, key),
      Tables.stored(Pawn.advance(board), width, ranks, key), Game.evaluate(Pawn.tree(limit, board)),
      Equal.cong(Chess.Board, Game.Outcome, input => Tables.stored(Pawn.advance(input), width, ranks, key),
        Index.decode_at(width, key), board, IndexProof.roundtrip_at(width, size, board)),
      Equal.trans(Game.Outcome, Tables.stored(Pawn.advance(board), width, ranks, key),
        Finite.get(width, Game.Outcome, key, Tables.solve(Pawn.advance(board), limit, width, limit, Tables.promotions(limit, width))),
        Game.evaluate(Pawn.tree(limit, board)), stored_board(board, width, limit, key), solved_board(limit, width, size, board))))

def serialized_value(+limit: Nat, +width: Nat, +size: {width == 20n : Nat}, +board: Chess.Board) ->
  {Finite.read(Tables.file(limit, width), Finite.offset(width, Index.encode_at(width, board))) ==
   Some{Game.byte(Game.evaluate(Pawn.tree(limit, board)))} : Maybe<&2, U32>}:
  +table = Tables.generate(limit, width)
  +key = Index.encode_at(width, board)
  +stored = Finite.get(width, U32, key, Pawnless.bytes(width, table))
  +value = Finite.get(width, Game.Outcome, key, table)
  +expected = Game.evaluate(Pawn.tree(limit, board))
  Equal.trans(Maybe<&2, U32>,
    Finite.read(Tables.file(limit, width), Finite.offset(width, key)), Some{stored}, Some{Game.byte(expected)},
    FiniteProof.read_go(width, Pawnless.bytes(width, table), key, Nil{}),
    Equal.trans(Maybe<&2, U32>, Some{stored}, Some{Game.byte(value)}, Some{Game.byte(expected)},
      Equal.cong(U32, Maybe<&2, U32>, byte => Some{byte}, stored, Game.byte(value), PawnlessProof.bytes_get(width, table, key)),
      Equal.cong(Game.Outcome, Maybe<&2, U32>, outcome => Some{Game.byte(outcome)}, value, expected,
        pointwise(limit, width, size, board))))

def file_length(+limit: Nat, +width: Nat) ->
  {List.length(&2, U32, Tables.file(limit, width)) == Finite.size(width) : Nat}:
  Equal.trans(Nat, List.length(&2, U32, Tables.file(limit, width)),
    Nat.add(Finite.size(width), 0n), Finite.size(width),
    FiniteProof.length_go(width, Pawnless.bytes(width, Tables.generate(limit, width)), Nil{}),
    PawnlessProof.add_zero(Finite.size(width)))
