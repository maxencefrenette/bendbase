import Base
import ./src/rules.bend as Rules
import ./src/position.bend as Position
import ./src/retrograde_logic.bend as Logic
import ./src/wdl_spec.bend as WDL
import ./src/clocked_wdl_spec.bend as Clocked
import ./src/rank_spec.bend as Ranked
import ./src/output.bend as Output
import ./src/encoding.bend as Encoding
import ./src/proof_tree.bend as ProofTree
import ./src/proof_queue.bend as ProofQueue
import ./src/retrograde.bend as Retro
import ./src/squares.bend as Squares
import ./src/clocked_step.bend as ClockedStep
import ./src/finite_wdl_spec.bend as Finite
import ./src/clocked_tables.bend as ClockedTables
import ./src/clocked_index.bend as ClockedIndex
import ./src/path_tree.bend as PathTree
import ./src/minimax_spec.bend as Minimax
import ./src/exact_spec.bend as Exact
import ./src/resource_wdl_spec.bend as Resource

def nonpawn_task(+kind: U32,
  task: Resource.NonpawnTask) -> Minimax.Task:
  match task:
    case Resource.WhiteValue{wk, bk,
        pc, clock}:
      Minimax.Value{kind,
        Rules.State{wk, bk, pc,
          0}, clock}
    case Resource.BlackValue{wk, bk,
        pc, clock}:
      Minimax.Value{kind,
        Rules.State{wk, bk, pc,
          1}, clock}
    case Resource.King{wk, bk, pc, clock}:
      Minimax.King{kind, wk, bk, pc, clock}
    case Resource.Piece{wk, bk, pc, clock}:
      Minimax.Piece{kind, wk, bk, pc, clock}
    case Resource.BlackAll{wk, bk, pc,
        clock, all_so_far}:
      Minimax.BlackAll{kind, wk, bk, pc,
        clock, all_so_far}

def CanonicalNonpawnPhase(phase: Nat,
  task: Resource.NonpawnTask) -> Type:
  match phase task:
    case 0n Resource.WhiteValue{wk,
        bk, pc, clock}:
      Empty
    case 1n Resource.WhiteValue{wk,
        bk, pc, clock}:
      Unit
    case 1n++more Resource.WhiteValue{
        wk, bk, pc, clock}:
      Empty
    case 0n Resource.BlackValue{wk,
        bk, pc, clock}:
      Empty
    case 1n Resource.BlackValue{wk,
        bk, pc, clock}:
      Unit
    case 1n++more Resource.BlackValue{
        wk, bk, pc, clock}:
      Empty
    case 0n Resource.King{wk, bk, pc, clock}:
      Unit
    case 1n+more Resource.King{
        wk, bk, pc, clock}:
      Empty
    case 0n Resource.Piece{wk, bk, pc, clock}:
      Unit
    case 1n+more Resource.Piece{
        wk, bk, pc, clock}:
      Empty
    case 0n Resource.BlackAll{wk, bk, pc,
        clock, all_so_far}:
      Unit
    case 1n+more Resource.BlackAll{
        wk, bk, pc, clock,
        all_so_far}:
      Empty

def nonpawn_phase(task: Resource.NonpawnTask) -> Nat:
  match task:
    case Resource.WhiteValue{wk, bk,
        pc, clock}:
      1n
    case Resource.BlackValue{wk, bk,
        pc, clock}:
      1n
    case _:
      0n

def Truth(b: Bool) -> Data:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

law minimax_has_move_matches_executable_scan:
  for +candidates: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +found: Bool
  {Minimax.has_move(candidates, kind,
    wk, bk, pc, found) ==
    Retro.black_has_move.squares(kind, wk,
      bk, pc, candidates, found) : Bool}

law minimax_has_move_has_witness:
  for +squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for yes: Truth(Minimax.has_move(
    squares, kind, wk, bk,
    pc, False{}))
  Finite.SomeSquare(dest =>
    WDL.Truth(Rules.black_move(kind,
      wk, bk, pc, dest)), squares)

law minimax_has_move_from_witness:
  for +squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for witness: Finite.SomeSquare(dest =>
    WDL.Truth(Rules.black_move(kind,
      wk, bk, pc, dest)), squares)
  Truth(Minimax.has_move(squares,
    kind, wk, bk, pc,
    False{}))

def MinimaxMateBool(+squares: List<&2, U32>,
  +kind: U32, +wk: U32, +bk: U32,
  +pc: U32) -> Bool:
  Rules.valid(kind,
    Rules.State{wk, bk, pc, 1}) &&
  (Bool.not(Minimax.has_move(squares,
    kind, wk, bk, pc,
    False{})) &&
   Rules.attacks(kind, pc,
     bk, wk))

law minimax_mate_sound:
  for +squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for complete: @dest: U32 ->
    Truth(U32.is_lt(dest, 64)) ->
    Squares.Member(U32, dest,
      squares)
  for +mate: Truth(MinimaxMateBool(
    squares, kind, wk, bk, pc))
  WDL.BlackMate(kind, wk, bk, pc)

law minimax_mate_complete:
  for +squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for mate: WDL.BlackMate(kind,
    wk, bk, pc)
  Truth(MinimaxMateBool(squares,
    kind, wk, bk, pc))

law minimax_zero_nonpawn_sound:
  for +squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +clock: Nat
  for complete: @dest: U32 ->
    Truth(U32.is_lt(dest, 64)) ->
    Squares.Member(U32, dest, squares)
  for +yes: Truth(Minimax.value(0n, clock,
    squares, kind,
    Rules.State{wk, bk, pc, 1}))
  WDL.BlackMate(kind, wk, bk, pc)

law minimax_zero_nonpawn_complete:
  for +squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +clock: Nat
  for +major: Truth(Bool.not(U32.is_eq(kind,
      2)) && Bool.not(U32.is_eq(kind, 3)))
  for mate: WDL.BlackMate(kind, wk, bk, pc)
  Truth(Minimax.value(0n, clock,
    squares, kind,
    Rules.State{wk, bk, pc, 1}))

law nonpawn_strategy_sound:
  for fuel: Nat
  for phase: Nat
  for +candidates: List<&2, U32>
  for +squares: List<&2, U32>
  for +kind: U32
  for task: Resource.NonpawnTask
  for phase_eq: {phase ==
    nonpawn_phase(task) : Nat}
  for +same: Truth(Squares.equals(
    squares, Squares.all6()))
  for +no_pawn: Truth(Bool.not(U32.is_eq(kind, 4)))
  for +yes: Truth(Minimax.win(fuel,
    phase, candidates, squares,
    nonpawn_task(kind, task)))
  Resource.NonpawnEvidence(fuel,
    phase, candidates, squares,
    kind, task)

law nonpawn_strategy_complete:
  for fuel: Nat
  for phase: Nat
  for +candidates: List<&2, U32>
  for +squares: List<&2, U32>
  for +kind: U32
  for task: Resource.NonpawnTask
  for phase_eq: {phase ==
    nonpawn_phase(task) : Nat}
  for +same: Truth(Squares.equals(
    squares, Squares.all6()))
  for +major: Truth(Bool.not(U32.is_eq(kind,
      2)) && Bool.not(U32.is_eq(kind, 3)))
  for +no_pawn: Truth(Bool.not(U32.is_eq(kind, 4)))
  for evidence: Resource.NonpawnEvidence(fuel,
    phase, candidates, squares,
    kind, task)
  Truth(Minimax.win(fuel,
    phase, candidates, squares,
    nonpawn_task(kind, task)))

def NonpawnBlackEvery(fuel: Nat,
  +clock: Nat,
  +squares: List<&2, U32>,
  +kind: U32,
  +wk: U32, +bk: U32,
  +pc: U32) -> Type:
  Finite.EverySquare(dest =>
    WDL.Truth(Rules.black_move(
      kind, wk, bk, pc, dest)) ->
    WDL.Truth(U32.is_ne(dest,
      pc)) &
    Resource.Nonpawn(fuel,
      1n+clock, squares,
      kind, Rules.State{wk,
        dest, pc, 0}),
    squares)

def pawn_task(task: Resource.PawnTask) ->
  Exact.Task:
  match task:
    case Resource.PawnWhiteValue{wk,
        bk, pc}:
      Exact.Value{4,
        Rules.State{wk, bk,
          pc, 0}}
    case Resource.PawnBlackValue{wk,
        bk, pc}:
      Exact.Value{4,
        Rules.State{wk, bk,
          pc, 1}}
    case Resource.PawnKing{wk, bk,
        pc}:
      Exact.King{4, wk, bk, pc}
    case Resource.PawnPiece{wk, bk,
        pc}:
      Exact.Piece{4, wk, bk, pc}
    case Resource.PawnBlackAll{wk, bk,
        pc, all_so_far}:
      Exact.BlackAll{4, wk,
        bk, pc, all_so_far}

def pawn_phase(task: Resource.PawnTask) -> Nat:
  match task:
    case Resource.PawnWhiteValue{wk,
        bk, pc}:
      1n
    case Resource.PawnBlackValue{wk,
        bk, pc}:
      1n
    case _:
      0n

law pawn_strategy_sound:
  for +pushes: Nat
  for remaining: Nat
  for phase: Nat
  for +candidates: List<&2, U32>
  for +squares: List<&2, U32>
  for task: Resource.PawnTask
  for phase_eq: {phase ==
    pawn_phase(task) : Nat}
  for +same: Truth(Squares.equals(
    squares, Squares.all6()))
  for +yes: Truth(Exact.win(pushes,
    remaining, phase, candidates,
    squares, pawn_task(task)))
  Resource.PawnEvidence(pushes,
    remaining, phase, candidates,
    squares, task)

law exact_pawn_king_scan_unfold:
  for +pushes: Nat
  for +clock_rest: Nat
  for +dest: U32
  for +tail: List<&2, U32>
  for +squares: List<&2, U32>
  for +wk: U32
  for +bk: U32
  for +pc: U32
  {Exact.win(pushes,
    1n+clock_rest, 0n,
    dest <> tail, squares,
    Exact.King{4, wk, bk, pc}) ==
   (Rules.move_to(4,
      Rules.State{wk, bk, pc, 0},
      Rules.State{dest, bk, pc, 1}) &&
    Exact.win(pushes, clock_rest,
      1n, squares, squares,
      Exact.Value{4,
        Rules.State{dest, bk, pc,
          1}})) ||
   Exact.win(pushes,
     1n+clock_rest, 0n,
     tail, squares,
     Exact.King{4, wk, bk, pc}) : Bool}

law exact_pawn_blackall_scan_unfold:
  for +pushes: Nat
  for +clock_rest: Nat
  for +dest: U32
  for +tail: List<&2, U32>
  for +squares: List<&2, U32>
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +all_so_far: Bool
  {Exact.win(pushes,
    1n+clock_rest, 0n,
    dest <> tail, squares,
    Exact.BlackAll{4, wk, bk,
      pc, all_so_far}) ==
   Exact.win(pushes,
     1n+clock_rest, 0n,
     tail, squares,
     Exact.BlackAll{4, wk, bk,
       pc, all_so_far &&
         (Bool.not(Rules.black_move(
           4, wk, bk, pc, dest)) ||
          (U32.is_ne(dest, pc) &&
           Exact.win(pushes,
             clock_rest, 1n,
             squares, squares,
             Exact.Value{4,
               Rules.State{wk, dest,
                 pc, 0}})))}) : Bool}

law pawn_strategy_complete:
  for +pushes: Nat
  for remaining: Nat
  for phase: Nat
  for +candidates: List<&2, U32>
  for +squares: List<&2, U32>
  for task: Resource.PawnTask
  for phase_eq: {phase ==
    pawn_phase(task) : Nat}
  for +same: Truth(Squares.equals(
    squares, Squares.all6()))
  for evidence: Resource.PawnEvidence(
    pushes, remaining, phase,
    candidates, squares, task)
  Truth(Exact.win(pushes,
    remaining, phase, candidates,
    squares, pawn_task(task)))

def PawnBlackEvery(pushes: Nat,
  clock_rest: Nat,
  +squares: List<&2, U32>,
  +wk: U32, +bk: U32,
  +pc: U32) -> Type:
  Finite.EverySquare(dest =>
    WDL.Truth(Rules.black_move(4,
      wk, bk, pc, dest)) ->
    WDL.Truth(U32.is_ne(dest,
      pc)) &
    Resource.Pawn(pushes,
      clock_rest, squares,
      Rules.State{wk, dest,
        pc, 0}), squares)

law nonpawn_white_value_strategy_sound:
  for +fuel: Nat
  for +clock: Nat
  for +squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +same: Truth(Squares.equals(
    squares, Squares.all6()))
  for +no_pawn: Truth(Bool.not(U32.is_eq(kind, 4)))
  for yes: Truth(Minimax.value(fuel,
    clock, squares, kind,
    Rules.State{wk, bk, pc, 0}))
  Resource.Nonpawn(fuel, clock,
    squares, kind,
    Rules.State{wk, bk, pc, 0})

law nonpawn_white_value_strategy_complete:
  for +fuel: Nat
  for +clock: Nat
  for +squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +same: Truth(Squares.equals(
    squares, Squares.all6()))
  for +major: Truth(Bool.not(U32.is_eq(kind,
      2)) && Bool.not(U32.is_eq(kind, 3)))
  for +no_pawn: Truth(Bool.not(U32.is_eq(kind, 4)))
  for evidence: Resource.Nonpawn(fuel,
    clock, squares, kind,
    Rules.State{wk, bk, pc, 0})
  Truth(Minimax.value(fuel,
    clock, squares, kind,
    Rules.State{wk, bk, pc, 0}))

law nonpawn_black_value_strategy_sound:
  for +fuel: Nat
  for +clock: Nat
  for +squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +same: Truth(Squares.equals(
    squares, Squares.all6()))
  for +no_pawn: Truth(Bool.not(U32.is_eq(kind, 4)))
  for yes: Truth(Minimax.value(fuel,
    clock, squares, kind,
    Rules.State{wk, bk, pc, 1}))
  Resource.Nonpawn(fuel, clock,
    squares, kind,
    Rules.State{wk, bk, pc, 1})

law nonpawn_black_value_strategy_complete:
  for +fuel: Nat
  for +clock: Nat
  for +squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +same: Truth(Squares.equals(
    squares, Squares.all6()))
  for +major: Truth(Bool.not(U32.is_eq(kind,
      2)) && Bool.not(U32.is_eq(kind, 3)))
  for +no_pawn: Truth(Bool.not(U32.is_eq(kind, 4)))
  for evidence: Resource.Nonpawn(fuel,
    clock, squares, kind,
    Rules.State{wk, bk, pc, 1})
  Truth(Minimax.value(fuel,
    clock, squares, kind,
    Rules.State{wk, bk, pc, 1}))

law promoted_strategy_sound:
  for +squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +same: Truth(Squares.equals(
    squares, Squares.all6()))
  for +no_pawn: Truth(Bool.not(U32.is_eq(kind, 4)))
  for +yes: Truth(Minimax.value(100n,
    0n, squares, kind,
    Rules.State{wk, bk, pc, 1}))
  Resource.Promoted(squares, kind,
    wk, bk, pc)

law promoted_strategy_complete_at:
  for +fuel: Nat
  for +squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +fuel_is_100: Truth(Nat.is_eq(
    fuel, 100n))
  for +same: Truth(Squares.equals(
    squares, Squares.all6()))
  for +major: Truth(Bool.not(U32.is_eq(kind,
      2)) && Bool.not(U32.is_eq(kind, 3)))
  for +no_pawn: Truth(Bool.not(U32.is_eq(kind, 4)))
  for evidence: Resource.Promoted(
    squares, kind, wk, bk, pc)
  Truth(Minimax.value(100n,
    0n, squares, kind,
    Rules.State{wk, bk, pc, 1}))

# A reusable, structural certificate for every leaf of a table. This is a
# Data proposition: it can be inspected for several successor moves without
# duplicating an affine universal function. Its proof is by tree induction,
# not by unfolding the concrete 2^19-leaf tree in the checker.
type BothData<-A: Data, -B: Data> is Data:
  Both{left: A, right: B}

def CanonicalCoverage(n: Nat,
  tree: PathTree.Tree<Word(n)>) -> Data:
  match n tree:
    case 0n PathTree.Leaf{word}:
      {word == WNil{} : Word(0n)}
    case 0n PathTree.Node{left, right}:
      Empty
    case 1n+rest PathTree.Leaf{word}:
      Empty
    case 1n+rest PathTree.Node{left, right}:
      BothData<
        {left == PathTree.prepend(rest,
          False{}, PathTree.drop_head(
            rest, left)) :
          PathTree.Tree<Word(1n+rest)>},
        BothData<
          CanonicalCoverage(rest,
            PathTree.drop_head(rest, left)),
          BothData<
            {right == PathTree.prepend(rest,
              True{}, PathTree.drop_head(
                rest, right)) :
              PathTree.Tree<Word(1n+rest)>},
            CanonicalCoverage(rest,
              PathTree.drop_head(rest,
                right))>>>

law path_tree_drop_head_prepend:
  for +n: Nat
  for +bit: Bool
  for +tree: PathTree.Tree<Word(n)>
  {PathTree.drop_head(n,
    PathTree.prepend(n, bit, tree)) ==
    tree : PathTree.Tree<Word(n)>}

law canonical_paths_have_coverage:
  for n: Nat
  CanonicalCoverage(n, PathTree.paths(n))

law canonical_paths_are_full:
  for n: Nat
  PathTree.Full(n, Word(n),
    PathTree.paths(n))

law path_tabulation_is_full:
  for n: Nat
  for +paths: PathTree.Tree<Word(19n)>
  for full: PathTree.Full(n,
    Word(19n), paths)
  for +kind: U32
  for +clock: Nat
  for +squares: List<&2, U32>
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  ProofTree.Full(n,
    ClockedTables.from_paths(paths,
      kind, clock, squares,
      next, reset, queen, rook))

law zero_path_tabulation_is_full:
  for n: Nat
  for +paths: PathTree.Tree<Word(19n)>
  for full: PathTree.Full(n,
    Word(19n), paths)
  ProofTree.Full(n,
    ClockedTables.zero_from_paths(paths))

law nonpawn_go_is_full:
  for +remaining: Nat
  for +clock: Nat
  for +kind: U32
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for full: PathTree.Full(19n,
    Word(19n), paths)
  for +zero: ProofTree.Tree
  ProofTree.Full(19n,
    ClockedTables.nonpawn.go(
      remaining, clock, kind,
      squares, paths, zero))

law pawn_clock_go_is_full:
  for +remaining: Nat
  for +clock: Nat
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for full: PathTree.Full(19n,
    Word(19n), paths)
  for +reset: ProofTree.Tree
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +zero: ProofTree.Tree
  ProofTree.Full(19n,
    ClockedTables.pawn.clock.go(
      remaining, clock, squares,
      paths, reset, queen, rook,
      zero))

law pawn_budget_go_is_full:
  for +pushes: Nat
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for full: PathTree.Full(19n,
    Word(19n), paths)
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +zero: ProofTree.Tree
  ProofTree.Full(19n,
    ClockedTables.pawn.budget.go(
      pushes, squares, paths,
      queen, rook, zero))

law canonical_coverage_lookup:
  for n: Nat
  for +tree: PathTree.Tree<Word(n)>
  for cover: CanonicalCoverage(n, tree)
  for +bits: Word(n)
  {PathTree.get(n, Word(n), tree,
    bits) == bits : Word(n)}

def MinimaxPathCorrect(+fuel: Nat, +clock: Nat,
  +kind: U32, +squares: List<&2, U32>,
  paths: PathTree.Tree<Word(19n)>,
  table: ProofTree.Tree) -> Data:
  match paths table:
    case PathTree.Leaf{path}
         ProofTree.Leaf{value}:
      {value == Minimax.value_at_path(fuel,
        clock, squares, kind, path) : U32}
    case PathTree.Node{left, right}
         ProofTree.Node{table_left, table_right}:
      BothData<
        MinimaxPathCorrect(fuel, clock, kind,
          squares, left, table_left),
        MinimaxPathCorrect(fuel, clock, kind,
          squares, right, table_right)>
    case _ _:
      Empty

def ExactPawnPathCorrect(+pushes: Nat,
  +remaining: Nat,
  +squares: List<&2, U32>,
  paths: PathTree.Tree<Word(19n)>,
  table: ProofTree.Tree) -> Data:
  match paths table:
    case PathTree.Leaf{path}
         ProofTree.Leaf{value}:
      {value == Exact.pawn_value_at_path(
        pushes, remaining, squares,
        path) : U32}
    case PathTree.Node{left, right}
         ProofTree.Node{table_left, table_right}:
      BothData<
        ExactPawnPathCorrect(pushes,
          remaining, squares, left,
          table_left),
        ExactPawnPathCorrect(pushes,
          remaining, squares, right,
          table_right)>
    case _ _:
      Empty

law exact_pawn_path_correct_lookup:
  for depth: Nat
  for +pushes: Nat
  for +remaining: Nat
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +table: ProofTree.Tree
  for cert: ExactPawnPathCorrect(pushes,
    remaining, squares, paths,
    table)
  for +bits: Word(depth)
  {ProofTree.get(depth, table, bits) ==
    Exact.pawn_value_at_path(pushes,
      remaining, squares,
      PathTree.get(depth, Word(19n),
        paths, bits)) : U32}

law exact_pawn_path_correct_canonical_index:
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n, paths)
  for +table: ProofTree.Tree
  for +pushes: Nat
  for +remaining: Nat
  for +squares: List<&2, U32>
  for cert: ExactPawnPathCorrect(pushes,
    remaining, squares, paths,
    table)
  for +low: Word(19n)
  {ProofTree.get_index(table,
    U32{Encoding.append(13n, 19n, low,
      Word.zero(13n))}) ==
    Bool.pick(U32,
      Exact.value(pushes, remaining,
        squares, 4,
        Rules.decode(U32{Encoding.append(
          13n, 19n, low,
          Word.zero(13n))})),
      1, 0) : U32}

law exact_pawn_path_correct_valid_state:
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n,
    paths)
  for +table: ProofTree.Tree
  for +pushes: Nat
  for +remaining: Nat
  for +squares: List<&2, U32>
  for cert: ExactPawnPathCorrect(pushes,
    remaining, squares, paths,
    table)
  for +state: Rules.State
  for +valid: Truth(Rules.valid(4,
    state))
  {ProofTree.get_index(table,
      Rules.index(state)) ==
    Bool.pick(U32,
      Exact.value(pushes,
        remaining, squares, 4,
        state), 1, 0) : U32}

law exact_pawn_path_correct_valid_state_bool:
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n, paths)
  for +table: ProofTree.Tree
  for +pushes: Nat
  for +remaining: Nat
  for +squares: List<&2, U32>
  for +cert: ExactPawnPathCorrect(pushes,
    remaining, squares, paths,
    table)
  for +state: Rules.State
  for +valid: Truth(Rules.valid(4, state))
  {U32.is_ne(ProofTree.get_index(table,
      Rules.index(state)), 0) ==
    Exact.value(pushes, remaining,
      squares, 4, state) : Bool}

law minimax_path_correct_lookup:
  for depth: Nat
  for +fuel: Nat
  for +clock: Nat
  for +kind: U32
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +table: ProofTree.Tree
  for cert: MinimaxPathCorrect(fuel, clock,
    kind, squares, paths, table)
  for +bits: Word(depth)
  {ProofTree.get(depth, table, bits) ==
    Minimax.value_at_path(fuel,
      clock, squares, kind,
      PathTree.get(depth, Word(19n),
        paths, bits)) : U32}

law minimax_path_correct_canonical_index:
  for +paths: PathTree.Tree<Word(19n)>
  for coverage: @bits: Word(19n) ->
    {PathTree.get(19n, Word(19n),
      paths, bits) == bits : Word(19n)}
  for +table: ProofTree.Tree
  for +fuel: Nat
  for +clock: Nat
  for +kind: U32
  for +squares: List<&2, U32>
  for cert: MinimaxPathCorrect(fuel,
    clock, kind, squares, paths, table)
  for +low: Word(19n)
  {ProofTree.get_index(table,
    U32{Encoding.append(13n, 19n, low,
      Word.zero(13n))}) ==
    Bool.pick(U32, Minimax.value(fuel,
      clock, squares, kind,
      Rules.decode(U32{Encoding.append(
        13n, 19n, low,
        Word.zero(13n))})), 1, 0) : U32}

law minimax_zero_horizon_white_matches_clock100_step:
  for +kind: U32
  for +squares: List<&2, U32>
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +zero: ProofTree.Tree
  {ClockedStep.value(kind, 100n,
    Rules.State{wk, bk, pc, 0},
    squares, zero, zero, zero, zero) ==
    Minimax.value(0n, 100n, squares,
      kind, Rules.State{wk, bk, pc, 0}) : Bool}

law minimax_zero_horizon_black_matches_clock100_step:
  for +kind: U32
  for +squares: List<&2, U32>
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +zero: ProofTree.Tree
  {ClockedStep.value(kind, 100n,
    Rules.State{wk, bk, pc, 1},
    squares, zero, zero, zero, zero) ==
    Minimax.value(0n, 100n, squares,
      kind, Rules.State{wk, bk, pc, 1}) : Bool}

law minimax_zero_horizon_canonical_low:
  for +low: Word(19n)
  for +kind: U32
  for +squares: List<&2, U32>
  for +zero: ProofTree.Tree
  {ClockedStep.value(kind, 100n,
    Rules.decode(U32{Encoding.append(13n,
      19n, low, Word.zero(13n))}),
    squares, zero, zero, zero, zero) ==
    Minimax.value(0n, 100n, squares,
      kind,
      Rules.decode(U32{Encoding.append(
        13n, 19n, low,
        Word.zero(13n))})) : Bool}

law minimax_nonpawn_base_certified:
  for +paths: PathTree.Tree<Word(19n)>
  for +kind: U32
  for +squares: List<&2, U32>
  for +zero: ProofTree.Tree
  MinimaxPathCorrect(0n, 100n, kind,
    squares, paths,
    ClockedTables.from_paths(paths, kind,
      100n, squares, zero, zero,
      zero, zero))

law truncate19_is_explicit_low_word:
  for +index: U32
  {Encoding.truncate19(index) ==
    U32{Encoding.append(13n, 19n,
      ClockedIndex.low19(index),
      Word.zero(13n))} : U32}

law valid_state_index_is_canonical_low_word:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +side: U32
  for valid: Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, side}))
  {Rules.index(Rules.State{wk, bk, pc,
    side}) ==
    U32{Encoding.append(13n, 19n,
      ClockedIndex.low19(Rules.index(
        Rules.State{wk, bk, pc, side})),
      Word.zero(13n))} : U32}

law minimax_path_correct_valid_state:
  for +paths: PathTree.Tree<Word(19n)>
  for coverage: @bits: Word(19n) ->
    {PathTree.get(19n, Word(19n),
      paths, bits) == bits : Word(19n)}
  for +table: ProofTree.Tree
  for +fuel: Nat
  for +clock: Nat
  for +kind: U32
  for +squares: List<&2, U32>
  for cert: MinimaxPathCorrect(fuel,
    clock, kind, squares, paths, table)
  for +state: Rules.State
  for +valid: Truth(Rules.valid(kind, state))
  {ProofTree.get_index(table,
    Rules.index(state)) ==
    Bool.pick(U32, Minimax.value(fuel,
      clock, squares, kind, state),
      1, 0) : U32}

law minimax_path_correct_valid_state_bool:
  for +paths: PathTree.Tree<Word(19n)>
  for coverage: @bits: Word(19n) ->
    {PathTree.get(19n, Word(19n),
      paths, bits) == bits : Word(19n)}
  for +table: ProofTree.Tree
  for +fuel: Nat
  for +clock: Nat
  for +kind: U32
  for +squares: List<&2, U32>
  for cert: MinimaxPathCorrect(fuel,
    clock, kind, squares, paths, table)
  for +state: Rules.State
  for valid: Truth(Rules.valid(kind, state))
  {U32.is_ne(ProofTree.get_index(table,
      Rules.index(state)), 0) ==
    Minimax.value(fuel, clock, squares,
      kind, state) : Bool}

law minimax_canonical_path_correct_valid_state_bool:
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n, paths)
  for +table: ProofTree.Tree
  for +fuel: Nat
  for +clock: Nat
  for +kind: U32
  for +squares: List<&2, U32>
  for +cert: MinimaxPathCorrect(fuel,
    clock, kind, squares, paths, table)
  for +state: Rules.State
  for valid: Truth(Rules.valid(kind, state))
  {U32.is_ne(ProofTree.get_index(table,
      Rules.index(state)), 0) ==
    Minimax.value(fuel, clock, squares,
      kind, state) : Bool}

law minimax_king_scan_matches_step:
  for +fuel: Nat
  for +clock: Nat
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +candidates: List<&2, U32>
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n, paths)
  for +next: ProofTree.Tree
  for +cert: MinimaxPathCorrect(fuel,
    1n+clock, kind, squares, paths, next)
  {ClockedStep.white_king.go(candidates,
    kind, Rules.State{wk, bk, pc, 0},
    wk, bk, pc, next) ==
    Minimax.win(1n+fuel, 0n, candidates,
      squares, Minimax.King{kind, wk,
        bk, pc, clock}) : Bool}

law nonpawn_piece_value_is_next:
  for +kind: U32
  for +pc: U32
  for +dest: U32
  for +target: Rules.State
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for no_pawn: Truth(Bool.not(U32.is_eq(
    kind, 4)))
  {ClockedStep.white_piece.value(kind,
    pc, dest, target, next, reset) ==
    ProofTree.get_index(next,
      Rules.index(target)) : U32}

law nonpawn_piece_clock_increments:
  for +kind: U32
  for +pc: U32
  for +dest: U32
  for +clock: Nat
  for no_pawn: Truth(Bool.not(U32.is_eq(
    kind, 4)))
  {Bool.pick(Nat, U32.is_eq(kind, 4) &&
    U32.is_ne(pc, dest), 0n,
    1n+clock) == 1n+clock : Nat}

law minimax_nonpawn_piece_scan_matches_step:
  for +fuel: Nat
  for +clock: Nat
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +candidates: List<&2, U32>
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n, paths)
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for +cert: MinimaxPathCorrect(fuel,
    1n+clock, kind, squares, paths, next)
  for +no_pawn: Truth(Bool.not(
    U32.is_eq(kind, 4)))
  {ClockedStep.white_piece.go(candidates,
    kind, Rules.State{wk, bk, pc, 0},
    wk, bk, pc, next, reset) ==
    Minimax.win(1n+fuel, 0n, candidates,
      squares, Minimax.Piece{kind, wk,
        bk, pc, clock}) : Bool}

def NotLT(c: Cmp) -> Type:
  match c:
    case LT{}:
      Empty
    case EQ{}:
      Unit
    case GT{}:
      Unit

law word_cmp_zero_not_lt:
  for n: Nat
  for +word: Word(n)
  NotLT(Word.cmp(n, word, Word.zero(n)))

law word_cmp_swap:
  for n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Encoding.flip_cmp(Word.cmp(n, a, b)) ==
    Word.cmp(n, b, a) : Cmp}

law word_cmp_self_eq:
  for n: Nat
  for +a: Word(n)
  {Word.cmp(n, a, a) == EQ{} : Cmp}

law u32_cmp_swap:
  for +a: U32
  for +b: U32
  {Encoding.flip_cmp(U32.cmp(a, b)) ==
    U32.cmp(b, a) : Cmp}

law u32_le_reflexive:
  for +a: U32
  Truth(U32.is_le(a, a))

law u32_max_upper_left:
  for +a: U32
  for +b: U32
  Truth(U32.is_le(a, U32.max(a, b)))

law u32_max_upper_right:
  for +a: U32
  for +b: U32
  Truth(U32.is_le(b, U32.max(a, b)))

law u32_max_preserves_upper_bound:
  for +a: U32
  for +b: U32
  for +limit: U32
  for a_bounded: Truth(U32.is_le(a, limit))
  for b_bounded: Truth(U32.is_le(b, limit))
  Truth(U32.is_le(U32.max(a, b), limit))

def CmpChain(ab: Cmp, bc: Cmp, ac: Cmp) -> Bool:
  match ab bc:
    case LT{} LT{}:
      Cmp.is_lt(ac)
    case LT{} EQ{}:
      Cmp.is_lt(ac)
    case LT{} GT{}:
      True{}
    case EQ{} LT{}:
      Cmp.is_lt(ac)
    case EQ{} EQ{}:
      Cmp.is_eq(ac)
    case EQ{} GT{}:
      Cmp.is_gt(ac)
    case GT{} LT{}:
      True{}
    case GT{} EQ{}:
      Cmp.is_gt(ac)
    case GT{} GT{}:
      Cmp.is_gt(ac)

law word_cmp_chain:
  for n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Word(n)
  Truth(CmpChain(Word.cmp(n, a, b),
    Word.cmp(n, b, c), Word.cmp(n, a, c)))

law u32_le_transitive:
  for +a: U32
  for +b: U32
  for +c: U32
  for ab: Truth(U32.is_le(a, b))
  for bc: Truth(U32.is_le(b, c))
  Truth(U32.is_le(a, c))

law word_inc_strict_below_ones:
  for n: Nat
  for +word: Word(n)
  for less: Truth(Cmp.is_lt(Word.cmp(n, word,
    Encoding.ones(n))))
  Truth(Cmp.is_lt(Word.cmp(n, word,
    Word.inc(n, word))))

law u32_all_ones_is_max:
  {U32{Encoding.ones(32n)} == 4294967295 : U32}

law u32_inc_strict_below_max:
  for +x: U32
  for less: Truth(U32.is_lt(x, 4294967295))
  Truth(U32.is_lt(x, U32.inc(x)))

law u32_le_lt_transitive:
  for +a: U32
  for +b: U32
  for +c: U32
  for ab: Truth(U32.is_le(a, b))
  for bc: Truth(U32.is_lt(b, c))
  Truth(U32.is_lt(a, c))

law word_cmp_zero_eq_implies_zero:
  for +n: Nat
  for +word: Word(n)
  for equal: Truth(Cmp.is_eq(
    Word.cmp(n, word, Word.zero(n))))
  {word == Word.zero(n) : Word(n)}

law word_lt_one_is_zero:
  for n: Nat
  for +word: Word(n)
  for less: Truth(Cmp.is_lt(
    Word.cmp(n, word, Encoding.one(n))))
  {word == Word.zero(n) : Word(n)}

law word_cmp_append_zero_prefix:
  for n: Nat
  for +m: Nat
  for +low: Word(n)
  for +high: Word(m)
  for +threshold: Word(m)
  {Word.cmp(Nat.add(n, m),
      Encoding.append(m, n, low, high),
      Encoding.append(m, n, Word.zero(n), threshold)) ==
    Encoding.cmp_low_zero(n, low,
      Word.cmp(m, high, threshold)) : Cmp}

law low_zero_prefix_lt_implies_high_lt:
  for n: Nat
  for +low: Word(n)
  for +high_cmp: Cmp
  for less: Truth(Cmp.is_lt(
    Encoding.cmp_low_zero(n, low, high_cmp)))
  Truth(Cmp.is_lt(high_cmp))

law structural_sixty_four_is_64:
  {U32{Encoding.append(26n, 6n,
    Word.zero(6n), Encoding.one(26n))} == 64 : U32}

law u32_under_64_is_canonical:
  for +x: U32
  for less: Truth(U32.is_lt(x, 64))
  {Encoding.square(Encoding.low6(x)) == x : U32}

law square_words_complete:
  for n: Nat
  for +word: Word(n)
  Squares.Member(Word(n), word, Squares.words(n))

law square_list_complete:
  for +x: U32
  for less: Truth(U32.is_lt(x, 64))
  Squares.Member(U32, x, Squares.all6())

law square_list_equals_refl:
  for +squares: List<&2, U32>
  Truth(Squares.equals(squares, squares))

law square_list_equals_member_transfer:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +value: U32
  for same: Truth(Squares.equals(xs, ys))
  for member: Squares.Member(U32,
    value, ys)
  Squares.Member(U32, value, xs)

law nat_equality_reflects_identity:
  for +a: Nat
  for +b: Nat
  for equal: Truth(Nat.is_eq(a, b))
  {a == b : Nat}

law structural_two_is_2:
  {U32{Encoding.append(31n, 1n,
    Word.zero(1n), Encoding.one(31n))} == 2 : U32}

law low_one_bit_matches_split:
  for +word: Word(32n)
  {Encoding.low1(U32{word}) ==
    Encoding.low1.fin(Encoding.split(31n, 1n, word)) : Bool}

law u32_under_2_is_canonical_turn:
  for +x: U32
  for less: Truth(U32.is_lt(x, 2))
  {Encoding.turn(WCon{Encoding.low1(x),
      Word.zero(13n)}) == x : U32}

law valid_implies_placement:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +side: U32
  for valid: Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, side}))
  Truth(Rules.placement_valid(kind, wk, bk, pc, side))

law placement_implies_ranges:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +side: U32
  for placement: Truth(Rules.placement_valid(
    kind, wk, bk, pc, side))
  Truth(U32.is_lt(side, 2)) &
  Truth(U32.is_lt(wk, 64)) &
  Truth(U32.is_lt(bk, 64)) &
  Truth(U32.is_lt(pc, 64))

law valid_state_index_roundtrip:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +side: U32
  for valid: Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, side}))
  {Rules.decode(Rules.index(
      Rules.State{wk, bk, pc, side})) ==
    Rules.State{wk, bk, pc, side} : Rules.State}

def array_value(read: Array<U32> & U32) -> U32:
  match read:
    case (array, value):
      value

law proof_tree_read_after_write:
  for n: Nat
  for +tree: ProofTree.Tree
  for +bits: Word(n)
  for +value: U32
  {ProofTree.get(n,
    ProofTree.set(n, tree, bits, value), bits) == value : U32}

law proof_tree_filled_get:
  for n: Nat
  for +value: U32
  for +bits: Word(n)
  {ProofTree.get(n, ProofTree.filled(n, value), bits) ==
    value : U32}

law proof_tree_filled_is_full:
  for n: Nat
  for +value: U32
  ProofTree.Full(n, ProofTree.filled(n, value))

law proof_tree_set_preserves_full:
  for n: Nat
  for +tree: ProofTree.Tree
  for +bits: Word(n)
  for +value: U32
  for full: ProofTree.Full(n, tree)
  ProofTree.Full(n, ProofTree.set(n, tree, bits, value))

law proof_tree_write_preserves_other:
  for n: Nat
  for +tree: ProofTree.Tree
  for +write_bits: Word(n)
  for +read_bits: Word(n)
  for +value: U32
  for full: ProofTree.Full(n, tree)
  for different: {write_bits != read_bits : Word(n)}
  {ProofTree.get(n,
      ProofTree.set(n, tree, write_bits, value),
      read_bits) ==
    ProofTree.get(n, tree, read_bits) : U32}

law proof_tree_index_read_after_write:
  for +tree: ProofTree.Tree
  for +index: U32
  for +value: U32
  {ProofTree.get_index(
      ProofTree.set_index(tree, index, value), index) ==
    value : U32}

law proof_tree_to_array_preserves_bytes:
  for +tree: ProofTree.Tree
  {Output.bytes(ProofTree.to_array(tree)) ==
    ProofTree.bytes(tree) : List<&2, U32>}

law proof_queue_pop_reassembles:
  for +queue: ProofQueue.Queue
  {ProofQueue.reassemble(ProofQueue.pop(queue)) ==
    ProofQueue.contents(queue) : List<&2, Rules.State>}

law state_list_append_associative:
  for +xs: List<&2, Rules.State>
  for +ys: List<&2, Rules.State>
  for +zs: List<&2, Rules.State>
  {List.append(&2, Rules.State, xs,
      List.append(&2, Rules.State, ys, zs)) ==
    List.append(&2, Rules.State,
      List.append(&2, Rules.State, xs, ys), zs) :
    List<&2, Rules.State>}

law state_list_reverse_go_appends_acc:
  for +xs: List<&2, Rules.State>
  for +prefix: List<&2, Rules.State>
  for +suffix: List<&2, Rules.State>
  {List.reverse.go(&2, Rules.State, xs,
      List.append(&2, Rules.State, prefix, suffix)) ==
    List.append(&2, Rules.State,
      List.reverse.go(&2, Rules.State, xs, prefix),
      suffix) : List<&2, Rules.State>}

law proof_queue_push_appends:
  for +queue: ProofQueue.Queue
  for +state: Rules.State
  {ProofQueue.contents(ProofQueue.push(queue, state)) ==
    List.append(&2, Rules.State,
      ProofQueue.contents(queue),
      state <> Nil{}) : List<&2, Rules.State>}

def QueuePopNone(read: ProofQueue.Queue &
  Maybe<&2, Rules.State>) -> Type:
  match read:
    case (queue, None{}):
      Unit
    case (queue, Some{state}):
      Empty

law proof_queue_empty_pop_means_empty_contents:
  for +queue: ProofQueue.Queue
  for none: QueuePopNone(ProofQueue.pop(queue))
  {ProofQueue.contents(queue) ==
    Nil{} : List<&2, Rules.State>}

def WorkFull(+work: Retro.Work) -> Type:
  match work:
    case Retro.Work{won, queue, squares}:
      ProofTree.Full(19n, won)

def WorkWonAt(work: Retro.Work, state: Rules.State) -> U32:
  match work:
    case Retro.Work{won, queue, squares}:
      ProofTree.get_index(won, Rules.index(state))

def WorkQueueContents(work: Retro.Work) ->
  List<&2, Rules.State>:
  match work:
    case Retro.Work{won, queue, squares}:
      ProofQueue.contents(queue)

def WorkSquares(work: Retro.Work) -> List<&2, U32>:
  match work:
    case Retro.Work{won, queue, squares}:
      squares

def WorkWonTree(work: Retro.Work) -> ProofTree.Tree:
  match work:
    case Retro.Work{won, queue, squares}:
      won

def WorkSquaresComplete(+work: Retro.Work) -> Type:
  @dest: U32 -> Truth(U32.is_lt(dest, 64)) ->
    Squares.Member(U32, dest, WorkSquares(work))

law retro_new_squares_complete:
  WorkSquaresComplete(Retro.new())

law retro_mark_new_keeps_squares:
  for +work: Retro.Work
  for +state: Rules.State
  for +rank: U32
  {WorkSquares(Retro.mark.new(work, state, rank)) ==
    WorkSquares(work) : List<&2, U32>}

law retro_mark_rank_keeps_squares:
  for +work: Retro.Work
  for +state: Rules.State
  for +rank: U32
  {WorkSquares(Retro.mark.rank(work, state, rank)) ==
    WorkSquares(work) : List<&2, U32>}

law retro_mark_rank_preserves_square_coverage:
  for +work: Retro.Work
  for +state: Rules.State
  for +rank: U32
  for complete: WorkSquaresComplete(work)
  WorkSquaresComplete(Retro.mark.rank(work,
    state, rank))

law retro_black_ready_keeps_squares:
  for +work: Retro.Work
  for +kind: U32
  for +state: Rules.State
  {WorkSquares(Retro.black_ready(work, kind, state)) ==
    WorkSquares(work) : List<&2, U32>}

law retro_predecessor_update_keeps_squares:
  for +work: Retro.Work
  for +kind: U32
  for +previous: Rules.State
  for +current: Rules.State
  for +turn: U32
  for +rank: U32
  {WorkSquares(Retro.predecessor.update(work, kind,
    previous, current, turn, rank)) ==
    WorkSquares(work) : List<&2, U32>}

law retro_previous_king_keeps_squares:
  for squares: List<&2, U32>
  for +work: Retro.Work
  for +kind: U32
  for +current: Rules.State
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +rank: U32
  {WorkSquares(Retro.previous_king.go(squares, kind,
    current, wk, bk, pc, rank, work)) ==
    WorkSquares(work) : List<&2, U32>}

law retro_previous_piece_keeps_squares:
  for squares: List<&2, U32>
  for +work: Retro.Work
  for +kind: U32
  for +current: Rules.State
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +rank: U32
  {WorkSquares(Retro.previous_piece.go(squares, kind,
    current, wk, bk, pc, rank, work)) ==
    WorkSquares(work) : List<&2, U32>}

law retro_previous_black_keeps_squares:
  for squares: List<&2, U32>
  for +work: Retro.Work
  for +kind: U32
  for +current: Rules.State
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +rank: U32
  {WorkSquares(Retro.previous_black.go(squares, kind,
    current, wk, bk, pc, rank, work)) ==
    WorkSquares(work) : List<&2, U32>}

law retro_predecessors_keep_squares:
  for +work: Retro.Work
  for +kind: U32
  for +current: Rules.State
  for +rank: U32
  {WorkSquares(Retro.predecessors(work, kind,
    current, rank)) ==
    WorkSquares(work) : List<&2, U32>}

law retro_predecessors_preserve_square_coverage:
  for +work: Retro.Work
  for +kind: U32
  for +current: Rules.State
  for +rank: U32
  for complete: WorkSquaresComplete(work)
  WorkSquaresComplete(Retro.predecessors(work,
    kind, current, rank))

def WorkTakeReassemble(read: Retro.Work &
  Maybe<&2, Rules.State>) -> List<&2, Rules.State>:
  match read:
    case (work, None{}):
      WorkQueueContents(work)
    case (work, Some{state}):
      state <> WorkQueueContents(work)

def WorkTakeSquares(read: Retro.Work &
  Maybe<&2, Rules.State>) -> List<&2, U32>:
  match read:
    case (work, state):
      WorkSquares(work)

def WorkRankReadSquares(read: Retro.Work & U32) ->
  List<&2, U32>:
  match read:
    case (work, rank):
      WorkSquares(work)

law retro_take_keeps_squares:
  for +work: Retro.Work
  {WorkTakeSquares(Retro.take(work)) ==
    WorkSquares(work) : List<&2, U32>}

law retro_marked_keeps_squares:
  for +work: Retro.Work
  for +index: U32
  {WorkRankReadSquares(Retro.marked(work, index)) ==
    WorkSquares(work) : List<&2, U32>}

law retro_propagate_rank_keeps_squares:
  for +kind: U32
  for +state: Rules.State
  for read: Retro.Work & U32
  {WorkSquares(Retro.propagate.rank(kind, state,
    read)) == WorkRankReadSquares(read) :
    List<&2, U32>}

law retro_propagate_consume_keeps_squares:
  for +kind: U32
  for read: Retro.Work & Maybe<&2, Rules.State>
  {WorkSquares(Retro.propagate.consume(kind, read)) ==
    WorkTakeSquares(read) : List<&2, U32>}

law retro_propagate_step_keeps_squares:
  for +kind: U32
  for +work: Retro.Work
  {WorkSquares(Retro.propagate.step(kind, work)) ==
    WorkSquares(work) : List<&2, U32>}

law retro_propagate_go_keeps_squares:
  for fuel: Nat
  for +kind: U32
  for +work: Retro.Work
  {WorkSquares(Retro.propagate.go(fuel, kind, work)) ==
    WorkSquares(work) : List<&2, U32>}

law retro_propagate_go_preserves_square_coverage:
  for fuel: Nat
  for +kind: U32
  for +work: Retro.Work
  for complete: WorkSquaresComplete(work)
  WorkSquaresComplete(Retro.propagate.go(
    fuel, kind, work))

law retro_init_state_keeps_squares:
  for +work: Retro.Work
  for +kind: U32
  for +index: U32
  {WorkSquares(Retro.init_state(work, kind, index)) ==
    WorkSquares(work) : List<&2, U32>}

law retro_init_go_keeps_squares:
  for fuel: Nat
  for +work: Retro.Work
  for +kind: U32
  for +index: U32
  {WorkSquares(Retro.init.go(fuel, kind, index,
    work)) == WorkSquares(work) : List<&2, U32>}

law retro_init_go_preserves_square_coverage:
  for fuel: Nat
  for +work: Retro.Work
  for +kind: U32
  for +index: U32
  for complete: WorkSquaresComplete(work)
  WorkSquaresComplete(Retro.init.go(fuel,
    kind, index, work))

def WorkTakeNone(read: Retro.Work &
  Maybe<&2, Rules.State>) -> Type:
  match read:
    case (work, None{}):
      Unit
    case (work, Some{state}):
      Empty

def BlackScanAll(scan: Retro.BlackReplyScan) -> Bool:
  match scan:
    case Retro.BlackReplyScan{seen, all_won, maximum}:
      all_won

law minimax_black_scan_all_matches_step:
  for +fuel: Nat
  for +clock: Nat
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +candidates: List<&2, U32>
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n, paths)
  for +next: ProofTree.Tree
  for +cert: MinimaxPathCorrect(fuel,
    1n+clock, kind, squares, paths, next)
  for +scan: Retro.BlackReplyScan
  {BlackScanAll(Retro.black_reply_scan.squares(
    kind, wk, bk, pc, candidates,
    next, scan)) ==
    Minimax.win(1n+fuel, 0n,
      candidates, squares,
      Minimax.BlackAll{kind, wk, bk,
        pc, clock, BlackScanAll(scan)}) : Bool}

law minimax_nonpawn_white_step_matches:
  for +fuel: Nat
  for +clock: Nat
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n, paths)
  for +next: ProofTree.Tree
  for +zero: ProofTree.Tree
  for +cert: MinimaxPathCorrect(fuel,
    1n+clock, kind, squares, paths, next)
  for +no_pawn: Truth(Bool.not(
    U32.is_eq(kind, 4)))
  {ClockedStep.value(kind, clock,
    Rules.State{wk, bk, pc, 0},
    squares, next, zero, zero, zero) ==
    Minimax.value(1n+fuel, clock,
      squares, kind,
      Rules.State{wk, bk, pc, 0}) : Bool}

law minimax_nonpawn_black_step_matches:
  for +fuel: Nat
  for +clock: Nat
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n, paths)
  for +next: ProofTree.Tree
  for +zero: ProofTree.Tree
  for +cert: MinimaxPathCorrect(fuel,
    1n+clock, kind, squares, paths, next)
  {ClockedStep.value(kind, clock,
    Rules.State{wk, bk, pc, 1},
    squares, next, zero, zero, zero) ==
    Minimax.value(1n+fuel, clock,
      squares, kind,
      Rules.State{wk, bk, pc, 1}) : Bool}

law minimax_nonpawn_step_canonical_low:
  for +low: Word(19n)
  for +fuel: Nat
  for +clock: Nat
  for +kind: U32
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n, paths)
  for +next: ProofTree.Tree
  for +zero: ProofTree.Tree
  for +cert: MinimaxPathCorrect(fuel,
    1n+clock, kind, squares, paths, next)
  for +no_pawn: Truth(Bool.not(
    U32.is_eq(kind, 4)))
  {ClockedStep.value(kind, clock,
    Rules.decode(U32{Encoding.append(13n,
      19n, low, Word.zero(13n))}),
    squares, next, zero, zero, zero) ==
    Minimax.value(1n+fuel, clock,
      squares, kind,
      Rules.decode(U32{Encoding.append(
        13n, 19n, low,
        Word.zero(13n))})) : Bool}

law minimax_nonpawn_layer_certified:
  for +subpaths: PathTree.Tree<Word(19n)>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n, paths)
  for +fuel: Nat
  for +clock: Nat
  for +kind: U32
  for +squares: List<&2, U32>
  for +next: ProofTree.Tree
  for +zero: ProofTree.Tree
  for +cert: MinimaxPathCorrect(fuel,
    1n+clock, kind, squares, paths, next)
  for +no_pawn: Truth(Bool.not(
    U32.is_eq(kind, 4)))
  MinimaxPathCorrect(1n+fuel, clock,
    kind, squares, subpaths,
    ClockedTables.from_paths(subpaths,
      kind, clock, squares, next,
      zero, zero, zero))

law minimax_nonpawn_go_certified:
  for +remaining: Nat
  for +clock: Nat
  for +kind: U32
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n, paths)
  for +zero: ProofTree.Tree
  for +no_pawn: Truth(Bool.not(
    U32.is_eq(kind, 4)))
  for budget: {Nat.add(clock,
    remaining) == 100n : Nat}
  MinimaxPathCorrect(remaining,
    clock, kind, squares, paths,
    ClockedTables.nonpawn.go(remaining,
      clock, kind, squares, paths,
      zero))

law exact_zero_push_white_pawn_is_draw:
  for remaining: Nat
  for +squares: List<&2, U32>
  for +wk: U32
  for +bk: U32
  for +pc: U32
  {Exact.value(0n, remaining,
    squares, 4, Rules.State{wk,
      bk, pc, 0}) == False{} : Bool}

law exact_zero_push_black_pawn_is_draw:
  for remaining: Nat
  for +squares: List<&2, U32>
  for +wk: U32
  for +bk: U32
  for +pc: U32
  {Exact.value(0n, remaining,
    squares, 4, Rules.State{wk,
      bk, pc, 1}) == False{} : Bool}

law exact_zero_push_canonical_low_is_draw:
  for +low: Word(19n)
  for remaining: Nat
  for +squares: List<&2, U32>
  {Exact.value(0n, remaining,
    squares, 4,
    Rules.decode(U32{Encoding.append(
      13n, 19n, low,
      Word.zero(13n))})) ==
    False{} : Bool}

law exact_pawn_zero_budget_certified:
  for +paths: PathTree.Tree<Word(19n)>
  for +remaining: Nat
  for +squares: List<&2, U32>
  ExactPawnPathCorrect(0n, remaining,
    squares, paths,
    ClockedTables.zero_from_paths(paths))

law exact_pawn_clock100_white_step_matches:
  for +push_rest: Nat
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +squares: List<&2, U32>
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  {ClockedStep.value(4, 100n,
    Rules.State{wk, bk, pc, 0},
    squares, next, reset, queen, rook) ==
    Exact.value(1n+push_rest, 0n,
      squares, 4,
      Rules.State{wk, bk, pc, 0}) : Bool}

law exact_pawn_clock100_black_step_matches:
  for +push_rest: Nat
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +squares: List<&2, U32>
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  {ClockedStep.value(4, 100n,
    Rules.State{wk, bk, pc, 1},
    squares, next, reset, queen, rook) ==
    Exact.value(1n+push_rest, 0n,
      squares, 4,
      Rules.State{wk, bk, pc, 1}) : Bool}

law exact_pawn_clock100_canonical_low_matches:
  for +low: Word(19n)
  for +push_rest: Nat
  for +squares: List<&2, U32>
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  {ClockedStep.value(4, 100n,
    Rules.decode(U32{Encoding.append(
      13n, 19n, low,
      Word.zero(13n))}),
    squares, next, reset, queen, rook) ==
    Exact.value(1n+push_rest, 0n,
      squares, 4,
      Rules.decode(U32{Encoding.append(
        13n, 19n, low,
        Word.zero(13n))})) : Bool}

law exact_pawn_clock_base_certified:
  for +paths: PathTree.Tree<Word(19n)>
  for +push_rest: Nat
  for +squares: List<&2, U32>
  for +zero: ProofTree.Tree
  for +reset: ProofTree.Tree
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  ExactPawnPathCorrect(1n+push_rest,
    0n, squares, paths,
    ClockedTables.from_paths(paths, 4,
      100n, squares, zero, reset,
      queen, rook))

law exact_pawn_king_scan_matches_step:
  for +push_rest: Nat
  for +clock_rest: Nat
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +candidates: List<&2, U32>
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n, paths)
  for +next: ProofTree.Tree
  for +cert: ExactPawnPathCorrect(
    1n+push_rest, clock_rest,
    squares, paths, next)
  {ClockedStep.white_king.go(candidates,
    4, Rules.State{wk, bk, pc, 0},
    wk, bk, pc, next) ==
    Exact.win(1n+push_rest,
      1n+clock_rest, 0n,
      candidates, squares,
      Exact.King{4, wk, bk, pc}) : Bool}

law exact_pawn_piece_scan_matches_step:
  for +push_rest: Nat
  for +clock_rest: Nat
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +candidates: List<&2, U32>
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n, paths)
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for +next_cert: ExactPawnPathCorrect(
    1n+push_rest, clock_rest,
    squares, paths, next)
  for +reset_cert: ExactPawnPathCorrect(
    push_rest, 100n,
    squares, paths, reset)
  {ClockedStep.white_piece.go(candidates,
    4, Rules.State{wk, bk, pc, 0},
    wk, bk, pc, next, reset) ==
    Exact.win(1n+push_rest,
      1n+clock_rest, 0n,
      candidates, squares,
      Exact.Piece{4, wk, bk, pc}) : Bool}

law exact_pawn_black_scan_all_matches_step:
  for +push_rest: Nat
  for +clock_rest: Nat
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +candidates: List<&2, U32>
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n, paths)
  for +next: ProofTree.Tree
  for +cert: ExactPawnPathCorrect(
    1n+push_rest, clock_rest,
    squares, paths, next)
  for +scan: Retro.BlackReplyScan
  {BlackScanAll(Retro.black_reply_scan.squares(
      4, wk, bk, pc, candidates, next,
      scan)) ==
    Exact.win(1n+push_rest,
      1n+clock_rest, 0n,
      candidates, squares,
      Exact.BlackAll{4, wk, bk, pc,
        BlackScanAll(scan)}) : Bool}

law exact_pawn_promotion_matches_step:
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n, paths)
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +queen_cert: MinimaxPathCorrect(
    100n, 0n, 0, squares, paths,
    queen)
  for +rook_cert: MinimaxPathCorrect(
    100n, 0n, 1, squares, paths,
    rook)
  {ClockedStep.white_promotion(wk, bk, pc,
      queen, rook) ==
    ((WDL.promotion(wk, bk, pc, 0,
        wk, bk, (pc + 8 : U32)) &&
      Minimax.value(100n, 0n,
        squares, 0,
        Rules.State{wk, bk,
          (pc + 8 : U32), 1})) ||
     (WDL.promotion(wk, bk, pc, 1,
        wk, bk, (pc + 8 : U32)) &&
      Minimax.value(100n, 0n,
        squares, 1,
        Rules.State{wk, bk,
          (pc + 8 : U32), 1}))) : Bool}

law exact_pawn_white_step_matches:
  for +push_rest: Nat
  for +clock_rest: Nat
  for +clock: Nat
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n, paths)
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +next_cert: ExactPawnPathCorrect(
    1n+push_rest, clock_rest,
    squares, paths, next)
  for +reset_cert: ExactPawnPathCorrect(
    push_rest, 100n,
    squares, paths, reset)
  for +queen_cert: MinimaxPathCorrect(
    100n, 0n, 0, squares, paths,
    queen)
  for +rook_cert: MinimaxPathCorrect(
    100n, 0n, 1, squares, paths,
    rook)
  for budget: {Nat.add(clock,
    1n+clock_rest) == 100n : Nat}
  {ClockedStep.value(4, clock,
      Rules.State{wk, bk, pc, 0},
      squares, next, reset,
      queen, rook) ==
    Exact.value(1n+push_rest,
      1n+clock_rest, squares, 4,
      Rules.State{wk, bk, pc, 0}) : Bool}

law exact_pawn_black_step_matches:
  for +push_rest: Nat
  for +clock_rest: Nat
  for +clock: Nat
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n, paths)
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +next_cert: ExactPawnPathCorrect(
    1n+push_rest, clock_rest,
    squares, paths, next)
  for budget: {Nat.add(clock,
    1n+clock_rest) == 100n : Nat}
  {ClockedStep.value(4, clock,
      Rules.State{wk, bk, pc, 1},
      squares, next, reset,
      queen, rook) ==
    Exact.value(1n+push_rest,
      1n+clock_rest, squares, 4,
      Rules.State{wk, bk, pc, 1}) : Bool}

law exact_pawn_step_canonical_low:
  for +low: Word(19n)
  for +push_rest: Nat
  for +clock_rest: Nat
  for +clock: Nat
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n, paths)
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +next_cert: ExactPawnPathCorrect(
    1n+push_rest, clock_rest,
    squares, paths, next)
  for +reset_cert: ExactPawnPathCorrect(
    push_rest, 100n,
    squares, paths, reset)
  for +queen_cert: MinimaxPathCorrect(
    100n, 0n, 0, squares, paths,
    queen)
  for +rook_cert: MinimaxPathCorrect(
    100n, 0n, 1, squares, paths,
    rook)
  for budget: {Nat.add(clock,
    1n+clock_rest) == 100n : Nat}
  {ClockedStep.value(4, clock,
      Rules.decode(U32{Encoding.append(
        13n, 19n, low,
        Word.zero(13n))}),
      squares, next, reset,
      queen, rook) ==
    Exact.value(1n+push_rest,
      1n+clock_rest, squares, 4,
      Rules.decode(U32{Encoding.append(
        13n, 19n, low,
        Word.zero(13n))})) : Bool}

law exact_pawn_layer_certified:
  for +subpaths: PathTree.Tree<Word(19n)>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n, paths)
  for +push_rest: Nat
  for +clock_rest: Nat
  for +clock: Nat
  for +squares: List<&2, U32>
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +next_cert: ExactPawnPathCorrect(
    1n+push_rest, clock_rest,
    squares, paths, next)
  for +reset_cert: ExactPawnPathCorrect(
    push_rest, 100n,
    squares, paths, reset)
  for +queen_cert: MinimaxPathCorrect(
    100n, 0n, 0, squares, paths,
    queen)
  for +rook_cert: MinimaxPathCorrect(
    100n, 0n, 1, squares, paths,
    rook)
  for +budget: {Nat.add(clock,
    1n+clock_rest) == 100n : Nat}
  ExactPawnPathCorrect(1n+push_rest,
    1n+clock_rest, squares,
    subpaths,
    ClockedTables.from_paths(subpaths,
      4, clock, squares, next,
      reset, queen, rook))

law exact_pawn_clock_go_certified:
  for +remaining: Nat
  for +clock: Nat
  for +push_rest: Nat
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n, paths)
  for +reset: ProofTree.Tree
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +zero: ProofTree.Tree
  for +reset_cert: ExactPawnPathCorrect(
    push_rest, 100n,
    squares, paths, reset)
  for +queen_cert: MinimaxPathCorrect(
    100n, 0n, 0, squares, paths,
    queen)
  for +rook_cert: MinimaxPathCorrect(
    100n, 0n, 1, squares, paths,
    rook)
  for +budget: {Nat.add(clock,
    remaining) == 100n : Nat}
  ExactPawnPathCorrect(1n+push_rest,
    remaining, squares, paths,
    ClockedTables.pawn.clock.go(
      remaining, clock, squares,
      paths, reset, queen, rook,
      zero))

law exact_pawn_budget_go_certified:
  for +pushes: Nat
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n, paths)
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +zero: ProofTree.Tree
  for +queen_cert: MinimaxPathCorrect(
    100n, 0n, 0, squares, paths,
    queen)
  for +rook_cert: MinimaxPathCorrect(
    100n, 0n, 1, squares, paths,
    rook)
  ExactPawnPathCorrect(pushes,
    100n, squares, paths,
    ClockedTables.pawn.budget.go(
      pushes, squares, paths,
      queen, rook, zero))

law generated_nonpawn_value_is_minimax:
  for +remaining: Nat
  for +clock: Nat
  for +kind: U32
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n,
    paths)
  for +zero: ProofTree.Tree
  for +no_pawn: Truth(Bool.not(
    U32.is_eq(kind, 4)))
  for budget: {Nat.add(clock,
    remaining) == 100n : Nat}
  for +state: Rules.State
  for valid: Truth(Rules.valid(kind,
    state))
  {U32.is_ne(ProofTree.get_index(
      ClockedTables.nonpawn.go(
        remaining, clock, kind,
        squares, paths, zero),
      Rules.index(state)), 0) ==
    Minimax.value(remaining, clock,
      squares, kind, state) : Bool}

law generated_pawn_value_is_exact:
  for +pushes: Nat
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n,
    paths)
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +zero: ProofTree.Tree
  for +queen_cert: MinimaxPathCorrect(
    100n, 0n, 0, squares, paths,
    queen)
  for +rook_cert: MinimaxPathCorrect(
    100n, 0n, 1, squares, paths,
    rook)
  for +state: Rules.State
  for valid: Truth(Rules.valid(4,
    state))
  {U32.is_ne(ProofTree.get_index(
      ClockedTables.pawn.budget.go(
        pushes, squares, paths,
        queen, rook, zero),
      Rules.index(state)), 0) ==
    Exact.value(pushes, 100n,
      squares, 4, state) : Bool}

law generated_nonpawn_byte_is_minimax:
  for +remaining: Nat
  for +clock: Nat
  for +kind: U32
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n,
    paths)
  for full: PathTree.Full(19n,
    Word(19n), paths)
  for +zero: ProofTree.Tree
  for +no_pawn: Truth(Bool.not(
    U32.is_eq(kind, 4)))
  for budget: {Nat.add(clock,
    remaining) == 100n : Nat}
  for +bits: Word(19n)
  {List.get(&2, U32,
      ProofTree.bytes(
        ClockedTables.nonpawn.go(
          remaining, clock, kind,
          squares, paths, zero)),
      ProofTree.byte_offset(19n,
        bits)) ==
    Some{Minimax.value_at_path(
      remaining, clock, squares,
      kind, PathTree.get(19n,
        Word(19n), paths,
        bits))} : Maybe<&2, U32>}

law generated_pawn_byte_is_exact:
  for +pushes: Nat
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n,
    paths)
  for full: PathTree.Full(19n,
    Word(19n), paths)
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +zero: ProofTree.Tree
  for +queen_cert: MinimaxPathCorrect(
    100n, 0n, 0, squares, paths,
    queen)
  for +rook_cert: MinimaxPathCorrect(
    100n, 0n, 1, squares, paths,
    rook)
  for +bits: Word(19n)
  {List.get(&2, U32,
      ProofTree.bytes(
        ClockedTables.pawn.budget.go(
          pushes, squares, paths,
          queen, rook, zero)),
      ProofTree.byte_offset(19n,
        bits)) ==
    Some{Exact.pawn_value_at_path(
      pushes, 100n, squares,
      PathTree.get(19n,
        Word(19n), paths,
        bits))} : Maybe<&2, U32>}

law generated_nonpawn_byte_canonical:
  for +remaining: Nat
  for +clock: Nat
  for +kind: U32
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n,
    paths)
  for full: PathTree.Full(19n,
    Word(19n), paths)
  for +zero: ProofTree.Tree
  for +no_pawn: Truth(Bool.not(
    U32.is_eq(kind, 4)))
  for budget: {Nat.add(clock,
    remaining) == 100n : Nat}
  for +bits: Word(19n)
  {List.get(&2, U32,
      ProofTree.bytes(
        ClockedTables.nonpawn.go(
          remaining, clock, kind,
          squares, paths, zero)),
      ProofTree.byte_offset(19n,
        bits)) ==
    Some{Minimax.value_at_path(
      remaining, clock, squares,
      kind, bits)} : Maybe<&2,
      U32>}

law generated_pawn_byte_canonical:
  for +pushes: Nat
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n,
    paths)
  for full: PathTree.Full(19n,
    Word(19n), paths)
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +zero: ProofTree.Tree
  for +queen_cert: MinimaxPathCorrect(
    100n, 0n, 0, squares, paths,
    queen)
  for +rook_cert: MinimaxPathCorrect(
    100n, 0n, 1, squares, paths,
    rook)
  for +bits: Word(19n)
  {List.get(&2, U32,
      ProofTree.bytes(
        ClockedTables.pawn.budget.go(
          pushes, squares, paths,
          queen, rook, zero)),
      ProofTree.byte_offset(19n,
        bits)) ==
    Some{Exact.pawn_value_at_path(
      pushes, 100n, squares,
      bits)} : Maybe<&2, U32>}

# Each generated entry is a White-win strategy exactly when its byte is
# nonzero. These statements are symbolic in the board coordinates and the
# resource budgets; neither asks the checker to inspect table positions.
law generated_nonpawn_strategy_sound:
  for +remaining: Nat
  for +clock: Nat
  for +kind: U32
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n,
    paths)
  for +zero: ProofTree.Tree
  for +no_pawn: Truth(Bool.not(
    U32.is_eq(kind, 4)))
  for budget: {Nat.add(clock,
    remaining) == 100n : Nat}
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +turn: Bool
  for +valid: Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc,
      Bool.pick(U32, turn, 1, 0)}))
  for +same: Truth(Squares.equals(
    squares, Squares.all6()))
  for yes: Truth(U32.is_ne(
    ProofTree.get_index(
      ClockedTables.nonpawn.go(
        remaining, clock, kind,
        squares, paths, zero),
      Rules.index(Rules.State{
        wk, bk, pc,
        Bool.pick(U32, turn, 1, 0)})),
    0))
  Resource.Nonpawn(remaining, clock,
    squares, kind,
    Rules.State{wk, bk, pc,
      Bool.pick(U32, turn, 1, 0)})

law generated_nonpawn_strategy_complete:
  for +remaining: Nat
  for +clock: Nat
  for +kind: U32
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n,
    paths)
  for +zero: ProofTree.Tree
  for +no_pawn: Truth(Bool.not(
    U32.is_eq(kind, 4)))
  for +major: Truth(
    Bool.not(U32.is_eq(kind, 2)) &&
    Bool.not(U32.is_eq(kind, 3)))
  for budget: {Nat.add(clock,
    remaining) == 100n : Nat}
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +turn: Bool
  for +valid: Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc,
      Bool.pick(U32, turn, 1, 0)}))
  for +same: Truth(Squares.equals(
    squares, Squares.all6()))
  for strategy: Resource.Nonpawn(
    remaining, clock, squares, kind,
    Rules.State{wk, bk, pc,
      Bool.pick(U32, turn, 1, 0)})
  Truth(U32.is_ne(
    ProofTree.get_index(
      ClockedTables.nonpawn.go(
        remaining, clock, kind,
        squares, paths, zero),
      Rules.index(Rules.State{
        wk, bk, pc,
        Bool.pick(U32, turn, 1, 0)})),
    0))

law generated_pawn_strategy_sound:
  for +pushes: Nat
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n,
    paths)
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +zero: ProofTree.Tree
  for +queen_cert: MinimaxPathCorrect(
    100n, 0n, 0, squares, paths,
    queen)
  for +rook_cert: MinimaxPathCorrect(
    100n, 0n, 1, squares, paths,
    rook)
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +turn: Bool
  for +valid: Truth(Rules.valid(4,
    Rules.State{wk, bk, pc,
      Bool.pick(U32, turn, 1, 0)}))
  for +same: Truth(Squares.equals(
    squares, Squares.all6()))
  for yes: Truth(U32.is_ne(
    ProofTree.get_index(
      ClockedTables.pawn.budget.go(
        pushes, squares, paths,
        queen, rook, zero),
      Rules.index(Rules.State{
        wk, bk, pc,
        Bool.pick(U32, turn, 1, 0)})),
    0))
  Resource.Pawn(pushes, 100n,
    squares, Rules.State{wk, bk,
      pc, Bool.pick(U32, turn,
        1, 0)})

law generated_pawn_strategy_complete:
  for +pushes: Nat
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n,
    paths)
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +zero: ProofTree.Tree
  for +queen_cert: MinimaxPathCorrect(
    100n, 0n, 0, squares, paths,
    queen)
  for +rook_cert: MinimaxPathCorrect(
    100n, 0n, 1, squares, paths,
    rook)
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +turn: Bool
  for +valid: Truth(Rules.valid(4,
    Rules.State{wk, bk, pc,
      Bool.pick(U32, turn, 1, 0)}))
  for +same: Truth(Squares.equals(
    squares, Squares.all6()))
  for strategy: Resource.Pawn(pushes,
    100n, squares,
    Rules.State{wk, bk, pc,
      Bool.pick(U32, turn, 1, 0)})
  Truth(U32.is_ne(
    ProofTree.get_index(
      ClockedTables.pawn.budget.go(
        pushes, squares, paths,
        queen, rook, zero),
      Rules.index(Rules.State{
        wk, bk, pc,
        Bool.pick(U32, turn, 1, 0)})),
    0))

law generated_nonpawn_serialized_valid_state:
  for +remaining: Nat
  for +clock: Nat
  for +kind: U32
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n,
    paths)
  for full: PathTree.Full(19n,
    Word(19n), paths)
  for +zero: ProofTree.Tree
  for +no_pawn: Truth(Bool.not(
    U32.is_eq(kind, 4)))
  for budget: {Nat.add(clock,
    remaining) == 100n : Nat}
  for +state: Rules.State
  for valid: Truth(Rules.valid(kind,
    state))
  {List.get(&2, U32,
      ProofTree.bytes(
        ClockedTables.nonpawn.go(
          remaining, clock, kind,
          squares, paths, zero)),
      ProofTree.byte_offset(19n,
        ProofTree.bits19(
          Rules.index(state)))) ==
    Some{Bool.pick(U32,
      Minimax.value(remaining,
        clock, squares, kind,
        state), 1, 0)} :
    Maybe<&2, U32>}

law generated_pawn_serialized_valid_state:
  for +pushes: Nat
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n,
    paths)
  for full: PathTree.Full(19n,
    Word(19n), paths)
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +zero: ProofTree.Tree
  for +queen_cert: MinimaxPathCorrect(
    100n, 0n, 0, squares, paths,
    queen)
  for +rook_cert: MinimaxPathCorrect(
    100n, 0n, 1, squares, paths,
    rook)
  for +state: Rules.State
  for valid: Truth(Rules.valid(4,
    state))
  {List.get(&2, U32,
      ProofTree.bytes(
        ClockedTables.pawn.budget.go(
          pushes, squares, paths,
          queen, rook, zero)),
      ProofTree.byte_offset(19n,
        ProofTree.bits19(
          Rules.index(state)))) ==
    Some{Bool.pick(U32,
      Exact.value(pushes, 100n,
        squares, 4, state),
      1, 0)} : Maybe<&2, U32>}

law nonpawn_serialized_byte_one_sound:
  for +remaining: Nat
  for +clock: Nat
  for +kind: U32
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n,
    paths)
  for full: PathTree.Full(19n,
    Word(19n), paths)
  for +zero: ProofTree.Tree
  for +no_pawn: Truth(Bool.not(
    U32.is_eq(kind, 4)))
  for budget: {Nat.add(clock,
    remaining) == 100n : Nat}
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +turn: Bool
  for +valid: Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc,
      Bool.pick(U32, turn, 1, 0)}))
  for +same: Truth(Squares.equals(
    squares, Squares.all6()))
  for read_one: {List.get(&2, U32,
    ProofTree.bytes(
      ClockedTables.nonpawn.go(
        remaining, clock, kind,
        squares, paths, zero)),
    ProofTree.byte_offset(19n,
      ProofTree.bits19(Rules.index(
        Rules.State{wk, bk, pc,
          Bool.pick(U32, turn,
            1, 0)})))) ==
    Some{1} : Maybe<&2, U32>}
  Resource.Nonpawn(remaining, clock,
    squares, kind,
    Rules.State{wk, bk, pc,
      Bool.pick(U32, turn,
        1, 0)})

law nonpawn_serialized_byte_one_complete:
  for +remaining: Nat
  for +clock: Nat
  for +kind: U32
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n,
    paths)
  for full: PathTree.Full(19n,
    Word(19n), paths)
  for +zero: ProofTree.Tree
  for +no_pawn: Truth(Bool.not(
    U32.is_eq(kind, 4)))
  for +major: Truth(
    Bool.not(U32.is_eq(kind, 2)) &&
    Bool.not(U32.is_eq(kind, 3)))
  for budget: {Nat.add(clock,
    remaining) == 100n : Nat}
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +turn: Bool
  for +valid: Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc,
      Bool.pick(U32, turn, 1, 0)}))
  for +same: Truth(Squares.equals(
    squares, Squares.all6()))
  for strategy: Resource.Nonpawn(
    remaining, clock, squares,
    kind, Rules.State{wk, bk, pc,
      Bool.pick(U32, turn,
        1, 0)})
  {List.get(&2, U32,
    ProofTree.bytes(
      ClockedTables.nonpawn.go(
        remaining, clock, kind,
        squares, paths, zero)),
    ProofTree.byte_offset(19n,
      ProofTree.bits19(Rules.index(
        Rules.State{wk, bk, pc,
          Bool.pick(U32, turn,
            1, 0)})))) ==
    Some{1} : Maybe<&2, U32>}

law pawn_serialized_byte_one_sound:
  for +pushes: Nat
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n,
    paths)
  for full: PathTree.Full(19n,
    Word(19n), paths)
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +zero: ProofTree.Tree
  for +queen_cert: MinimaxPathCorrect(
    100n, 0n, 0, squares,
    paths, queen)
  for +rook_cert: MinimaxPathCorrect(
    100n, 0n, 1, squares,
    paths, rook)
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +turn: Bool
  for +valid: Truth(Rules.valid(4,
    Rules.State{wk, bk, pc,
      Bool.pick(U32, turn, 1, 0)}))
  for +same: Truth(Squares.equals(
    squares, Squares.all6()))
  for read_one: {List.get(&2, U32,
    ProofTree.bytes(
      ClockedTables.pawn.budget.go(
        pushes, squares, paths,
        queen, rook, zero)),
    ProofTree.byte_offset(19n,
      ProofTree.bits19(Rules.index(
        Rules.State{wk, bk, pc,
          Bool.pick(U32, turn,
            1, 0)})))) ==
    Some{1} : Maybe<&2, U32>}
  Resource.Pawn(pushes, 100n,
    squares, Rules.State{wk,
      bk, pc, Bool.pick(U32,
        turn, 1, 0)})

law pawn_serialized_byte_one_complete:
  for +pushes: Nat
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n,
    paths)
  for full: PathTree.Full(19n,
    Word(19n), paths)
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +zero: ProofTree.Tree
  for +queen_cert: MinimaxPathCorrect(
    100n, 0n, 0, squares,
    paths, queen)
  for +rook_cert: MinimaxPathCorrect(
    100n, 0n, 1, squares,
    paths, rook)
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +turn: Bool
  for +valid: Truth(Rules.valid(4,
    Rules.State{wk, bk, pc,
      Bool.pick(U32, turn, 1, 0)}))
  for +same: Truth(Squares.equals(
    squares, Squares.all6()))
  for strategy: Resource.Pawn(pushes,
    100n, squares,
    Rules.State{wk, bk, pc,
      Bool.pick(U32, turn,
        1, 0)})
  {List.get(&2, U32,
    ProofTree.bytes(
      ClockedTables.pawn.budget.go(
        pushes, squares, paths,
        queen, rook, zero)),
    ProofTree.byte_offset(19n,
      ProofTree.bits19(Rules.index(
        Rules.State{wk, bk, pc,
          Bool.pick(U32, turn,
            1, 0)})))) ==
    Some{1} : Maybe<&2, U32>}

law nonpawn_serialized_byte_zero_refutes_win:
  for +remaining: Nat
  for +clock: Nat
  for +kind: U32
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n,
    paths)
  for full: PathTree.Full(19n,
    Word(19n), paths)
  for +zero: ProofTree.Tree
  for +no_pawn: Truth(Bool.not(
    U32.is_eq(kind, 4)))
  for +major: Truth(
    Bool.not(U32.is_eq(kind, 2)) &&
    Bool.not(U32.is_eq(kind, 3)))
  for budget: {Nat.add(clock,
    remaining) == 100n : Nat}
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +turn: Bool
  for +valid: Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc,
      Bool.pick(U32, turn, 1, 0)}))
  for +same: Truth(Squares.equals(
    squares, Squares.all6()))
  for read_zero: {List.get(&2, U32,
    ProofTree.bytes(
      ClockedTables.nonpawn.go(
        remaining, clock, kind,
        squares, paths, zero)),
    ProofTree.byte_offset(19n,
      ProofTree.bits19(Rules.index(
        Rules.State{wk, bk, pc,
          Bool.pick(U32, turn,
            1, 0)})))) ==
    Some{0} : Maybe<&2, U32>}
  for strategy: Resource.Nonpawn(
    remaining, clock, squares,
    kind, Rules.State{wk, bk, pc,
      Bool.pick(U32, turn,
        1, 0)})
  Empty

law pawn_serialized_byte_zero_refutes_win:
  for +pushes: Nat
  for +squares: List<&2, U32>
  for +paths: PathTree.Tree<Word(19n)>
  for +cover: CanonicalCoverage(19n,
    paths)
  for full: PathTree.Full(19n,
    Word(19n), paths)
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +zero: ProofTree.Tree
  for +queen_cert: MinimaxPathCorrect(
    100n, 0n, 0, squares,
    paths, queen)
  for +rook_cert: MinimaxPathCorrect(
    100n, 0n, 1, squares,
    paths, rook)
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +turn: Bool
  for +valid: Truth(Rules.valid(4,
    Rules.State{wk, bk, pc,
      Bool.pick(U32, turn, 1, 0)}))
  for +same: Truth(Squares.equals(
    squares, Squares.all6()))
  for read_zero: {List.get(&2, U32,
    ProofTree.bytes(
      ClockedTables.pawn.budget.go(
        pushes, squares, paths,
        queen, rook, zero)),
    ProofTree.byte_offset(19n,
      ProofTree.bits19(Rules.index(
        Rules.State{wk, bk, pc,
          Bool.pick(U32, turn,
            1, 0)})))) ==
    Some{0} : Maybe<&2, U32>}
  for strategy: Resource.Pawn(pushes,
    100n, squares,
    Rules.State{wk, bk, pc,
      Bool.pick(U32, turn,
        1, 0)})
  Empty

def BlackScanSeen(scan: Retro.BlackReplyScan) -> Bool:
  match scan:
    case Retro.BlackReplyScan{seen, all_won, maximum}:
      seen

def BlackScanMaximum(scan: Retro.BlackReplyScan) -> U32:
  match scan:
    case Retro.BlackReplyScan{seen, all_won, maximum}:
      maximum

law clocked_black_value_fin_unfold:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +scan: Retro.BlackReplyScan
  {ClockedStep.black_value.fin(kind,
    wk, bk, pc, scan) ==
    (Bool.not(BlackScanSeen(scan)) &&
      Rules.attacks(kind, pc, bk, wk)) ||
    (BlackScanSeen(scan) &&
      BlackScanAll(scan)) : Bool}

def BlackScanBound(squares: List<&2, U32>,
  +kind: U32, +wk: U32, +bk: U32, +pc: U32,
  +won: ProofTree.Tree, +maximum: U32) -> Type:
  match squares:
    case Nil{}:
      Unit
    case dest <> rest:
      (Truth(Rules.black_move(kind, wk, bk, pc, dest)) ->
        Truth(U32.is_le(ProofTree.get_index(won,
          Rules.index(Rules.State{wk, dest, pc, 0})),
          maximum))) &
      BlackScanBound(rest, kind, wk, bk, pc,
        won, maximum)

law black_reply_consider_max_monotone:
  for +scan: Retro.BlackReplyScan
  for +rank: U32
  for +capture: Bool
  for legal: Bool
  Truth(U32.is_le(BlackScanMaximum(scan),
    BlackScanMaximum(Retro.black_reply_consider(
      scan, rank, capture, legal))))

law black_reply_consider_max_covers_new:
  for +scan: Retro.BlackReplyScan
  for +rank: U32
  for +capture: Bool
  for legal: Bool
  for yes: Truth(legal)
  Truth(U32.is_le(rank,
    BlackScanMaximum(Retro.black_reply_consider(
      scan, rank, capture, legal))))

law black_reply_square_scan_max_monotone:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +won: ProofTree.Tree
  for +scan: Retro.BlackReplyScan
  Truth(U32.is_le(BlackScanMaximum(scan),
    BlackScanMaximum(Retro.black_reply_scan.squares(
      kind, wk, bk, pc, squares, won, scan))))

law black_reply_square_scan_max_bounds_legal:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +won: ProofTree.Tree
  for +scan: Retro.BlackReplyScan
  BlackScanBound(squares, kind, wk, bk, pc, won,
    BlackScanMaximum(Retro.black_reply_scan.squares(
      kind, wk, bk, pc, squares, won, scan)))

law black_scan_bound_member:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for +won: ProofTree.Tree
  for +maximum: U32
  for member: Squares.Member(U32, dest, squares)
  for bound: BlackScanBound(squares, kind, wk, bk,
    pc, won, maximum)
  for move: Truth(Rules.black_move(kind, wk, bk, pc,
    dest))
  Truth(U32.is_le(ProofTree.get_index(won,
    Rules.index(Rules.State{wk, dest, pc, 0})),
    maximum))

law work_black_reply_scan_max_bounds_legal_move:
  for +work: Retro.Work
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for complete: WorkSquaresComplete(work)
  for valid: Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, 1}))
  for +move: Truth(Rules.black_move(kind, wk, bk, pc,
    dest))
  Truth(U32.is_le(ProofTree.get_index(
    WorkWonTree(work), Rules.index(
      Rules.State{wk, dest, pc, 0})),
    BlackScanMaximum(Retro.black_reply_scan(kind,
      Rules.State{wk, bk, pc, 1},
      WorkWonTree(work), WorkSquares(work)))))

law work_black_reply_rank_decreases_if_no_overflow:
  for +work: Retro.Work
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for complete: WorkSquaresComplete(work)
  for valid: Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, 1}))
  for +move: Truth(Rules.black_move(kind, wk, bk, pc,
    dest))
  for room: Truth(U32.is_lt(
    BlackScanMaximum(Retro.black_reply_scan(kind,
      Rules.State{wk, bk, pc, 1},
      WorkWonTree(work), WorkSquares(work))),
    4294967295))
  Truth(U32.is_lt(ProofTree.get_index(
    WorkWonTree(work), Rules.index(
      Rules.State{wk, dest, pc, 0})),
    U32.inc(BlackScanMaximum(Retro.black_reply_scan(
      kind, Rules.State{wk, bk, pc, 1},
      WorkWonTree(work), WorkSquares(work))))))

def BlackScanSegment(fuel: Nat, +kind: U32,
  +wk: U32, +bk: U32, +pc: U32, +dest: U32,
  +won: ProofTree.Tree) -> Type:
  match fuel:
    case 0n:
      Unit
    case 1n+rest:
      (Truth(Rules.black_move(kind, wk, bk, pc, dest)) ->
        Truth(Bool.not(U32.is_eq(dest, pc))) &
        Truth(U32.is_ne(ProofTree.get_index(won,
          Rules.index(Rules.State{wk, dest, pc, 0})), 0))) &
      BlackScanSegment(rest, kind, wk, bk, pc,
        (dest + 1 : U32), won)

def BlackLegalSegment(fuel: Nat, +kind: U32,
  +wk: U32, +bk: U32, +pc: U32, +dest: U32) -> Type:
  match fuel:
    case 0n:
      Empty
    case 1n+rest:
      Truth(Rules.black_move(kind, wk, bk, pc, dest)) |
      BlackLegalSegment(rest, kind, wk, bk, pc,
        (dest + 1 : U32))

def BlackScanSquares(squares: List<&2, U32>,
  +kind: U32, +wk: U32, +bk: U32, +pc: U32,
  +won: ProofTree.Tree) -> Type:
  match squares:
    case Nil{}:
      Unit
    case dest <> rest:
      (Truth(Rules.black_move(kind, wk, bk, pc, dest)) ->
        Truth(Bool.not(U32.is_eq(dest, pc))) &
        Truth(U32.is_ne(ProofTree.get_index(won,
          Rules.index(Rules.State{wk, dest, pc, 0})), 0))) &
      BlackScanSquares(rest, kind, wk, bk, pc, won)

def BlackRepliesWon(+kind: U32, +wk: U32,
  +bk: U32, +pc: U32, +won: ProofTree.Tree) -> Type:
  @dest: U32 ->
    Truth(Rules.black_move(kind, wk, bk, pc, dest)) ->
    Truth(Bool.not(U32.is_eq(dest, pc))) &
    Truth(U32.is_ne(ProofTree.get_index(won,
      Rules.index(Rules.State{wk, dest, pc, 0})), 0))

def BlackLegalSquares(squares: List<&2, U32>,
  +kind: U32, +wk: U32, +bk: U32, +pc: U32) -> Type:
  match squares:
    case Nil{}:
      Empty
    case dest <> rest:
      Truth(Rules.black_move(kind, wk, bk, pc, dest)) |
      BlackLegalSquares(rest, kind, wk, bk, pc)

law black_scan_squares_sound_to_global:
  for +squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +won: ProofTree.Tree
  for +valid: Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, 1}))
  for complete: @dest: U32 ->
    Truth(U32.is_lt(dest, 64)) ->
    Squares.Member(U32, dest, squares)
  for safe: BlackScanSquares(squares, kind,
    wk, bk, pc, won)
  BlackRepliesWon(kind, wk, bk, pc, won)

def WhiteKingWinningSquares(
  squares: List<&2, U32>, +kind: U32,
  +wk: U32, +bk: U32, +pc: U32,
  +next: ProofTree.Tree) -> Type:
  match squares:
    case Nil{}:
      Empty
    case dest <> rest:
      (Truth(Rules.move_to(kind,
        Rules.State{wk, bk, pc, 0},
        Rules.State{dest, bk, pc, 1})) &
       Truth(U32.is_ne(ProofTree.get_index(next,
        Rules.index(Rules.State{dest, bk, pc, 1})), 0))) |
      WhiteKingWinningSquares(rest, kind, wk, bk,
        pc, next)

def WhitePieceWinningSquares(
  squares: List<&2, U32>, +kind: U32,
  +wk: U32, +bk: U32, +pc: U32,
  +next: ProofTree.Tree,
  +reset: ProofTree.Tree) -> Type:
  match squares:
    case Nil{}:
      Empty
    case dest <> rest:
      (Truth(Rules.move_to(kind,
        Rules.State{wk, bk, pc, 0},
        Rules.State{wk, bk, dest, 1})) &
       Truth(U32.is_ne(
        ClockedStep.white_piece.value(kind, pc,
          dest, Rules.State{wk, bk, dest, 1},
          next, reset), 0))) |
      WhitePieceWinningSquares(rest, kind, wk, bk,
        pc, next, reset)

def WhiteKingWinningWitness(+kind: U32,
  +wk: U32, +bk: U32, +pc: U32,
  +next: ProofTree.Tree) -> Type:
  &dest: U32 ->
    Truth(Rules.move_to(kind,
      Rules.State{wk, bk, pc, 0},
      Rules.State{dest, bk, pc, 1})) &
    Truth(U32.is_ne(ProofTree.get_index(next,
      Rules.index(Rules.State{dest, bk, pc, 1})),
      0))

def WhitePieceWinningWitness(+kind: U32,
  +wk: U32, +bk: U32, +pc: U32,
  +next: ProofTree.Tree,
  +reset: ProofTree.Tree) -> Type:
  &dest: U32 ->
    Truth(Rules.move_to(kind,
      Rules.State{wk, bk, pc, 0},
      Rules.State{wk, bk, dest, 1})) &
    Truth(U32.is_ne(
      ClockedStep.white_piece.value(kind, pc,
        dest, Rules.State{wk, bk, dest, 1},
        next, reset), 0))

law white_king_squares_have_witness:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +next: ProofTree.Tree
  for found: WhiteKingWinningSquares(squares,
    kind, wk, bk, pc, next)
  WhiteKingWinningWitness(kind, wk, bk, pc, next)

law finite_some_white_king_matches_scan:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +next: ProofTree.Tree
  Finite.SomeSquare(dest =>
    WDL.Truth(Rules.move_to(kind,
      Rules.State{wk, bk, pc, 0},
      Rules.State{dest, bk, pc, 1})) &
    WDL.Truth(U32.is_ne(ProofTree.get_index(next,
      Rules.index(Rules.State{dest, bk, pc, 1})),
      0)), squares) ->
  WhiteKingWinningSquares(squares, kind, wk,
    bk, pc, next)

law white_king_scan_matches_finite_some:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +next: ProofTree.Tree
  for found: WhiteKingWinningSquares(squares,
    kind, wk, bk, pc, next)
  Finite.SomeSquare(dest =>
    WDL.Truth(Rules.move_to(kind,
      Rules.State{wk, bk, pc, 0},
      Rules.State{dest, bk, pc, 1})) &
    WDL.Truth(U32.is_ne(ProofTree.get_index(next,
      Rules.index(Rules.State{dest, bk, pc, 1})),
      0)), squares)

law finite_some_white_piece_matches_scan:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for found: Finite.SomeSquare(dest =>
    WDL.Truth(Rules.move_to(kind,
      Rules.State{wk, bk, pc, 0},
      Rules.State{wk, bk, dest, 1})) &
    WDL.Truth(U32.is_ne(
      ClockedStep.white_piece.value(kind, pc,
        dest, Rules.State{wk, bk, dest, 1},
        next, reset), 0)), squares)
  WhitePieceWinningSquares(squares, kind, wk,
    bk, pc, next, reset)

law white_piece_scan_matches_finite_some:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for found: WhitePieceWinningSquares(squares,
    kind, wk, bk, pc, next, reset)
  Finite.SomeSquare(dest =>
    WDL.Truth(Rules.move_to(kind,
      Rules.State{wk, bk, pc, 0},
      Rules.State{wk, bk, dest, 1})) &
    WDL.Truth(U32.is_ne(
      ClockedStep.white_piece.value(kind, pc,
        dest, Rules.State{wk, bk, dest, 1},
        next, reset), 0)), squares)

law finite_every_black_matches_scan:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +next: ProofTree.Tree
  for all: Finite.EverySquare(dest =>
    WDL.Truth(Rules.black_move(kind, wk,
      bk, pc, dest)) ->
    WDL.Truth(U32.is_ne(dest, pc)) &
    WDL.Truth(U32.is_ne(ProofTree.get_index(
      next, Rules.index(Rules.State{
        wk, dest, pc, 0})), 0)), squares)
  BlackScanSquares(squares, kind, wk,
    bk, pc, next)

law black_scan_matches_finite_every:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +next: ProofTree.Tree
  for all: BlackScanSquares(squares,
    kind, wk, bk, pc, next)
  Finite.EverySquare(dest =>
    WDL.Truth(Rules.black_move(kind, wk,
      bk, pc, dest)) ->
    WDL.Truth(U32.is_ne(dest, pc)) &
    WDL.Truth(U32.is_ne(ProofTree.get_index(
      next, Rules.index(Rules.State{
        wk, dest, pc, 0})), 0)), squares)

law finite_black_some_matches_legal_squares:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for found: Finite.SomeSquare(dest =>
    WDL.Truth(Rules.black_move(kind, wk,
      bk, pc, dest)), squares)
  BlackLegalSquares(squares, kind, wk, bk, pc)

law black_legal_squares_match_finite_some:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for found: BlackLegalSquares(squares,
    kind, wk, bk, pc)
  Finite.SomeSquare(dest =>
    WDL.Truth(Rules.black_move(kind, wk,
      bk, pc, dest)), squares)

law white_piece_squares_have_witness:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for found: WhitePieceWinningSquares(squares,
    kind, wk, bk, pc, next, reset)
  WhitePieceWinningWitness(kind, wk, bk, pc,
    next, reset)

law white_king_move_destination_in_range:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for legal: Truth(Rules.move_to(kind,
    Rules.State{wk, bk, pc, 0},
    Rules.State{dest, bk, pc, 1}))
  Truth(U32.is_lt(dest, 64))

law white_piece_move_destination_in_range:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for legal: Truth(Rules.move_to(kind,
    Rules.State{wk, bk, pc, 0},
    Rules.State{wk, bk, dest, 1}))
  Truth(U32.is_lt(dest, 64))

law white_king_winning_square_is_scanned:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for +next: ProofTree.Tree
  for member: Squares.Member(U32, dest, squares)
  for legal: Truth(Rules.move_to(kind,
    Rules.State{wk, bk, pc, 0},
    Rules.State{dest, bk, pc, 1}))
  for yes: Truth(U32.is_ne(ProofTree.get_index(next,
    Rules.index(Rules.State{dest, bk, pc, 1})),
    0))
  WhiteKingWinningSquares(squares, kind, wk,
    bk, pc, next)

law white_piece_winning_square_is_scanned:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for member: Squares.Member(U32, dest, squares)
  for legal: Truth(Rules.move_to(kind,
    Rules.State{wk, bk, pc, 0},
    Rules.State{wk, bk, dest, 1}))
  for yes: Truth(U32.is_ne(
    ClockedStep.white_piece.value(kind, pc,
      dest, Rules.State{wk, bk, dest, 1},
      next, reset), 0))
  WhitePieceWinningSquares(squares, kind, wk,
    bk, pc, next, reset)

law clocked_step_white_king_scan_sound:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +next: ProofTree.Tree
  for yes: Truth(ClockedStep.white_king.go(squares,
    kind, Rules.State{wk, bk, pc, 0}, wk, bk,
    pc, next))
  WhiteKingWinningSquares(squares, kind, wk,
    bk, pc, next)

law clocked_step_white_king_scan_complete:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +next: ProofTree.Tree
  for witness: WhiteKingWinningSquares(
    squares, kind, wk, bk, pc, next)
  Truth(ClockedStep.white_king.go(squares,
    kind, Rules.State{wk, bk, pc, 0}, wk, bk,
    pc, next))

law clocked_step_white_piece_scan_sound:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for yes: Truth(ClockedStep.white_piece.go(squares,
    kind, Rules.State{wk, bk, pc, 0}, wk, bk,
    pc, next, reset))
  WhitePieceWinningSquares(squares, kind, wk,
    bk, pc, next, reset)

law clocked_step_white_piece_scan_complete:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for witness: WhitePieceWinningSquares(
    squares, kind, wk, bk, pc, next, reset)
  Truth(ClockedStep.white_piece.go(squares,
    kind, Rules.State{wk, bk, pc, 0}, wk, bk,
    pc, next, reset))

law clocked_table_write_slot_reads_step:
  for +kind: U32
  for +clock: Nat
  for +squares: List<&2, U32>
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +index: U32
  for +tree: ProofTree.Tree
  {ProofTree.get_index(ClockedTables.write_slot(
    kind, clock, squares, next, reset,
    queen, rook, index, tree), index) ==
    Bool.pick(U32, ClockedStep.value(kind,
      clock, Rules.decode(index), squares,
      next, reset, queen, rook), 1, 0) : U32}

law clocked_table_write_slot_preserves_full:
  for +kind: U32
  for +clock: Nat
  for +squares: List<&2, U32>
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +index: U32
  for +tree: ProofTree.Tree
  for full: ProofTree.Full(19n, tree)
  ProofTree.Full(19n, ClockedTables.write_slot(
    kind, clock, squares, next, reset,
    queen, rook, index, tree))

law clocked_table_step_preserves_full:
  for fuel: Nat
  for +index: U32
  for +kind: U32
  for +clock: Nat
  for +squares: List<&2, U32>
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +tree: ProofTree.Tree
  for full: ProofTree.Full(19n, tree)
  ProofTree.Full(19n, ClockedTables.step.go(
    fuel, index, kind, clock, squares,
    next, reset, queen, rook, tree))

law clocked_tabulate_reads_its_path:
  for n: Nat
  for +prefix: U32
  for +kind: U32
  for +clock: Nat
  for +squares: List<&2, U32>
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +bits: Word(n)
  {ProofTree.get(n, ClockedTables.tabulate.go(
    n, prefix, kind, clock, squares,
    next, reset, queen, rook), bits) ==
    Bool.pick(U32, ClockedStep.value(kind,
      clock,
      Rules.decode(ClockedTables.path_index(
        n, prefix, bits)), squares,
      next, reset, queen, rook), 1, 0) : U32}

law clocked_tabulate_is_full:
  for n: Nat
  for +prefix: U32
  for +kind: U32
  for +clock: Nat
  for +squares: List<&2, U32>
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  ProofTree.Full(n, ClockedTables.tabulate.go(
    n, prefix, kind, clock, squares,
    next, reset, queen, rook))

law clocked_index_reverse_snoc:
  for n: Nat
  for +word: Word(n)
  for +bit: Bool
  {ClockedIndex.reverse(1n+n,
    ClockedIndex.snoc(n, word, bit)) ==
    WCon{bit, ClockedIndex.reverse(n, word)} :
    Word(1n+n)}

law clocked_index_reverse_involution:
  for n: Nat
  for +word: Word(n)
  {ClockedIndex.reverse(n,
    ClockedIndex.reverse(n, word)) ==
    word : Word(n)}

law clocked_index_matches_existing_bits:
  for +index: U32
  {ProofTree.bits19(index) ==
    ClockedIndex.path(index) : Word(19n)}

law clocked_index_path_of_low_word:
  for +low: Word(19n)
  {ClockedIndex.path(U32{Encoding.append(
    13n, 19n, low, Word.zero(13n))}) ==
    ClockedIndex.reverse(19n, low) :
    Word(19n)}

law path_tree_prepend_lookup:
  for depth: Nat
  for n: Nat
  for +bit: Bool
  for +tree: PathTree.Tree<Word(n)>
  for +bits: Word(depth)
  {PathTree.get(depth, Word(1n+n),
    PathTree.prepend(n, bit, tree), bits) ==
    WCon{bit, PathTree.get(depth,
      Word(n), tree, bits)} : Word(1n+n)}

law path_tree_lookup_is_path:
  for n: Nat
  for +bits: Word(n)
  {PathTree.get(n, Word(n),
    PathTree.paths(n), bits) == bits : Word(n)}

def CertifiedPathTree(n: Nat) -> Type:
  &tree: PathTree.Tree<Word(n)> ->
    @bits: Word(n) ->
      {PathTree.get(n, Word(n), tree,
        bits) == bits : Word(n)}

law structural_path_tree_is_certified:
  for +n: Nat
  CertifiedPathTree(n)

law canonical_path_tree_lookup:
  for n: Nat
  for +tree: PathTree.Tree<Word(n)>
  for +same: {tree == PathTree.paths(n) :
    PathTree.Tree<Word(n)>}
  for +bits: Word(n)
  {PathTree.get(n, Word(n), tree,
    bits) == bits : Word(n)}

law clocked_path_tabulation_lookup:
  for depth: Nat
  for +tree: PathTree.Tree<Word(19n)>
  for +kind: U32
  for +clock: Nat
  for +squares: List<&2, U32>
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +bits: Word(depth)
  {ProofTree.get(depth,
    ClockedTables.from_paths(tree, kind,
      clock, squares, next, reset,
      queen, rook), bits) ==
    ClockedTables.value_at_path(kind, clock,
      squares, next, reset, queen, rook,
      PathTree.get(depth, Word(19n), tree,
        bits)) : U32}

law clocked_tabulated_path_has_its_value:
  for +tree: PathTree.Tree<Word(19n)>
  for +kind: U32
  for +clock: Nat
  for +squares: List<&2, U32>
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +bits: Word(19n)
  for path: {PathTree.get(19n, Word(19n),
    tree, bits) == bits : Word(19n)}
  {ProofTree.get(19n,
    ClockedTables.from_paths(tree, kind,
      clock, squares, next, reset,
      queen, rook), bits) ==
    ClockedTables.value_at_path(kind,
      clock, squares, next, reset,
      queen, rook, bits) : U32}

law clocked_tabulation_reads_canonical_index:
  for +tree: PathTree.Tree<Word(19n)>
  for coverage: @bits: Word(19n) ->
    {PathTree.get(19n, Word(19n), tree,
      bits) == bits : Word(19n)}
  for +kind: U32
  for +clock: Nat
  for +squares: List<&2, U32>
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +low: Word(19n)
  {ProofTree.get_index(
    ClockedTables.from_paths(tree, kind,
      clock, squares, next, reset,
      queen, rook),
    U32{Encoding.append(13n, 19n, low,
      Word.zero(13n))}) ==
    Bool.pick(U32, ClockedStep.value(kind,
      clock,
      Rules.decode(U32{Encoding.append(
        13n, 19n, low, Word.zero(13n))}),
      squares, next, reset, queen, rook),
      1, 0) : U32}

law nonpawn_base_reads_step:
  for +tree: PathTree.Tree<Word(19n)>
  for coverage: @bits: Word(19n) ->
    {PathTree.get(19n, Word(19n), tree,
      bits) == bits : Word(19n)}
  for +kind: U32
  for +clock: Nat
  for +squares: List<&2, U32>
  for +zero: ProofTree.Tree
  for +low: Word(19n)
  {ProofTree.get_index(
    ClockedTables.nonpawn.go(0n, clock,
      kind, squares, tree, zero),
    U32{Encoding.append(13n, 19n, low,
      Word.zero(13n))}) ==
    Bool.pick(U32, ClockedStep.value(kind,
      clock,
      Rules.decode(U32{Encoding.append(
        13n, 19n, low, Word.zero(13n))}),
      squares, zero, zero, zero, zero),
      1, 0) : U32}

law nonpawn_step_reads_next:
  for +remaining: Nat
  for +tree: PathTree.Tree<Word(19n)>
  for coverage: @bits: Word(19n) ->
    {PathTree.get(19n, Word(19n), tree,
      bits) == bits : Word(19n)}
  for +kind: U32
  for +clock: Nat
  for +squares: List<&2, U32>
  for +zero: ProofTree.Tree
  for +low: Word(19n)
  {ProofTree.get_index(
    ClockedTables.nonpawn.go(1n+remaining,
      clock, kind, squares, tree, zero),
    U32{Encoding.append(13n, 19n, low,
      Word.zero(13n))}) ==
    Bool.pick(U32, ClockedStep.value(kind,
      clock,
      Rules.decode(U32{Encoding.append(
        13n, 19n, low, Word.zero(13n))}),
      squares,
      ClockedTables.nonpawn.go(remaining,
        1n+clock, kind, squares, tree, zero),
      zero, zero, zero), 1, 0) : U32}

law clocked_step_at_hundred_white_is_draw:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +squares: List<&2, U32>
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  {ClockedStep.value(kind, 100n,
    Rules.State{wk, bk, pc, 0}, squares,
    next, reset, queen, rook) ==
    False{} : Bool}

law clocked_step_at_hundred_black_is_mate:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +squares: List<&2, U32>
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  {ClockedStep.value(kind, 100n,
    Rules.State{wk, bk, pc, 1}, squares,
    next, reset, queen, rook) ==
    (Rules.valid(kind,
      Rules.State{wk, bk, pc, 1}) &&
      Bool.not(U32.is_eq(kind, 2)) &&
      Bool.not(U32.is_eq(kind, 3)) &&
      ClockedStep.black_terminal(kind, wk,
        bk, pc, squares)) : Bool}

def BlackLegalWitness(+kind: U32, +wk: U32,
  +bk: U32, +pc: U32) -> Type:
  &dest: U32 -> Truth(Rules.black_move(kind,
    wk, bk, pc, dest))

law black_legal_squares_has_witness:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for legal: BlackLegalSquares(squares,
    kind, wk, bk, pc)
  BlackLegalWitness(kind, wk, bk, pc)

law black_legal_witness_is_a_game_move:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for valid: Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, 1}))
  for legal: BlackLegalWitness(kind, wk, bk, pc)
  WDL.BlackHasMove(kind, wk, bk, pc)

law game_black_move_has_legal_destination:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for game_move: WDL.BlackHasMove(kind, wk,
    bk, pc)
  BlackLegalWitness(kind, wk, bk, pc)

law clocked_step_black_terminal_sound:
  for +squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +valid: Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, 1}))
  for complete: @dest: U32 ->
    Truth(U32.is_lt(dest, 64)) ->
    Squares.Member(U32, dest, squares)
  for +terminal: Truth(ClockedStep.black_terminal(
    kind, wk, bk, pc, squares))
  WDL.BlackMate(kind, wk, bk, pc)

law clocked_step_black_terminal_complete:
  for +squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for mate: WDL.BlackMate(kind, wk, bk, pc)
  Truth(ClockedStep.black_terminal(kind, wk,
    bk, pc, squares))

def BlackClockStep(squares: List<&2, U32>,
  +kind: U32, +clock: Nat,
  +wk: U32, +bk: U32, +pc: U32,
  +next: ProofTree.Tree) -> Type:
  WDL.BlackMate(kind, wk, bk, pc) |
  (WDL.Truth(Nat.is_lt(clock, 100n)) &
   BlackLegalSquares(squares, kind, wk, bk,
     pc) &
   BlackScanSquares(squares, kind, wk,
     bk, pc, next))

law clocked_black_step_sound:
  for +squares: List<&2, U32>
  for +kind: U32
  for +clock: Nat
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +next: ProofTree.Tree
  for +valid: Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, 1}))
  for complete_mate: @dest: U32 ->
    Truth(U32.is_lt(dest, 64)) ->
    Squares.Member(U32, dest, squares)
  for complete_scan: @dest: U32 ->
    Truth(U32.is_lt(dest, 64)) ->
    Squares.Member(U32, dest, squares)
  for yes: Truth(ClockedStep.value.valid(kind,
    clock, Rules.State{wk, bk, pc, 1},
    squares, next, next, next, next))
  BlackClockStep(squares, kind, clock,
    wk, bk, pc, next)

law clocked_black_step_complete:
  for +squares: List<&2, U32>
  for +kind: U32
  for +clock: Nat
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +next: ProofTree.Tree
  for evidence: BlackClockStep(squares,
    kind, clock, wk, bk, pc, next)
  Truth(ClockedStep.value.valid(kind,
    clock, Rules.State{wk, bk, pc, 1},
    squares, next, next, next, next))

def WhitePromotionStep(+wk: U32, +bk: U32,
  +pc: U32, +queen: ProofTree.Tree,
  +rook: ProofTree.Tree) -> Type:
  +target = (pc + 8 : U32)
  +index = Rules.index(Rules.State{
    wk, bk, target, 1})
  (Truth(WDL.promotion(wk, bk, pc,
     0, wk, bk, target)) &
   Truth(U32.is_ne(ProofTree.get_index(
     queen, index), 0))) |
  (Truth(WDL.promotion(wk, bk, pc,
     1, wk, bk, target)) &
   Truth(U32.is_ne(ProofTree.get_index(
     rook, index), 0)))

def WhiteClockChoices(squares: List<&2, U32>,
  +kind: U32,
  +wk: U32, +bk: U32, +pc: U32,
  +next: ProofTree.Tree,
  +reset: ProofTree.Tree,
  +queen: ProofTree.Tree,
  +rook: ProofTree.Tree) -> Type:
  (WhiteKingWinningSquares(squares,
      kind, wk, bk, pc, next) |
    WhitePieceWinningSquares(squares,
      kind, wk, bk, pc, next, reset)) |
  (Truth(U32.is_eq(kind, 4)) &
   WhitePromotionStep(wk, bk, pc,
     queen, rook))

def WhiteClockStep(squares: List<&2, U32>,
  +kind: U32, +clock: Nat,
  +wk: U32, +bk: U32, +pc: U32,
  +next: ProofTree.Tree,
  +reset: ProofTree.Tree,
  +queen: ProofTree.Tree,
  +rook: ProofTree.Tree) -> Type:
  Truth(Nat.is_lt(clock, 100n)) &
  WhiteClockChoices(squares, kind, wk, bk,
    pc, next, reset, queen, rook)

law clocked_white_step_sound:
  for +squares: List<&2, U32>
  for +kind: U32
  for +clock: Nat
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for +yes: Truth(ClockedStep.value.valid(kind,
    clock, Rules.State{wk, bk, pc, 0},
    squares, next, reset, queen, rook))
  WhiteClockStep(squares, kind, clock,
    wk, bk, pc, next, reset, queen, rook)

law clocked_white_step_complete:
  for +squares: List<&2, U32>
  for +kind: U32
  for +clock: Nat
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  for +queen: ProofTree.Tree
  for +rook: ProofTree.Tree
  for evidence: WhiteClockStep(squares,
    kind, clock, wk, bk, pc,
    next, reset, queen, rook)
  Truth(ClockedStep.value.valid(kind,
    clock, Rules.State{wk, bk, pc, 0},
    squares, next, reset, queen, rook))

law black_reply_square_scan_all_sound:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +won: ProofTree.Tree
  for +scan: Retro.BlackReplyScan
  for all: Truth(BlackScanAll(Retro.black_reply_scan.squares(
    kind, wk, bk, pc, squares, won, scan)))
  BlackScanSquares(squares, kind, wk, bk, pc, won)

law black_reply_square_scan_all_complete:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +won: ProofTree.Tree
  for +scan: Retro.BlackReplyScan
  for initial: Truth(BlackScanAll(scan))
  for safe: BlackScanSquares(squares, kind, wk, bk, pc, won)
  Truth(BlackScanAll(Retro.black_reply_scan.squares(
    kind, wk, bk, pc, squares, won, scan)))

law black_reply_square_scan_seen_complete:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +won: ProofTree.Tree
  for +scan: Retro.BlackReplyScan
  for legal: BlackLegalSquares(squares, kind, wk, bk, pc)
  Truth(BlackScanSeen(Retro.black_reply_scan.squares(
    kind, wk, bk, pc, squares, won, scan)))

law black_has_move_squares_complete:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +found: Bool
  for legal: BlackLegalSquares(squares, kind, wk, bk, pc)
  Truth(Retro.black_has_move.squares(kind, wk, bk,
    pc, squares, found))

law black_has_move_squares_sound:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for yes: Truth(Retro.black_has_move.squares(kind,
    wk, bk, pc, squares, False{}))
  BlackLegalSquares(squares, kind, wk, bk, pc)

law black_reply_scan_seen_matches_has_move:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +won: ProofTree.Tree
  for +scan: Retro.BlackReplyScan
  {BlackScanSeen(Retro.black_reply_scan.squares(
    kind, wk, bk, pc, squares, won, scan)) ==
    Retro.black_has_move.squares(kind, wk, bk,
      pc, squares, BlackScanSeen(scan)) : Bool}

law clocked_step_pawn_reset_matches_game_clock:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for +next: ProofTree.Tree
  for +reset: ProofTree.Tree
  {ClockedStep.white_piece.value(kind, pc, dest,
    Rules.State{wk, bk, dest, 1}, next, reset) ==
    Bool.pick(U32,
      Clocked.zeroing(WDL.White{kind, wk, bk, pc},
        WDL.Black{kind, wk, bk, dest}),
      ProofTree.get_index(reset,
        Rules.index(Rules.State{wk, bk, dest, 1})),
      ProofTree.get_index(next,
        Rules.index(Rules.State{wk, bk, dest, 1}))) : U32}

law black_scan_legal_member:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for member: Squares.Member(U32, dest, squares)
  for move: Truth(Rules.black_move(kind, wk, bk, pc, dest))
  BlackLegalSquares(squares, kind, wk, bk, pc)

law black_scan_safe_member:
  for squares: List<&2, U32>
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for +won: ProofTree.Tree
  for member: Squares.Member(U32, dest, squares)
  for safe: BlackScanSquares(squares, kind, wk, bk, pc, won)
  for move: Truth(Rules.black_move(kind, wk, bk, pc, dest))
  Truth(Bool.not(U32.is_eq(dest, pc))) &
  Truth(U32.is_ne(ProofTree.get_index(won,
    Rules.index(Rules.State{wk, dest, pc, 0})), 0))

law black_reply_scan_all_sound:
  for fuel: Nat
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for +won: ProofTree.Tree
  for +scan: Retro.BlackReplyScan
  for all: Truth(BlackScanAll(Retro.black_reply_scan.go(
    fuel, kind, wk, bk, pc, dest, won, scan)))
  BlackScanSegment(fuel, kind, wk, bk, pc, dest, won)

law black_reply_scan_all_complete:
  for fuel: Nat
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for +won: ProofTree.Tree
  for +scan: Retro.BlackReplyScan
  for initial_all: Truth(BlackScanAll(scan))
  for segment: BlackScanSegment(fuel, kind, wk, bk, pc,
    dest, won)
  Truth(BlackScanAll(Retro.black_reply_scan.go(
    fuel, kind, wk, bk, pc, dest, won, scan)))

law black_reply_scan_seen_complete:
  for fuel: Nat
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for +won: ProofTree.Tree
  for +scan: Retro.BlackReplyScan
  for legal: BlackLegalSegment(fuel, kind, wk, bk,
    pc, dest)
  Truth(BlackScanSeen(Retro.black_reply_scan.go(
    fuel, kind, wk, bk, pc, dest, won, scan)))

law black_has_move_complete:
  for fuel: Nat
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for +found: Bool
  for legal: BlackLegalSegment(fuel, kind, wk, bk,
    pc, dest)
  Truth(Retro.black_has_move.go(fuel, kind, wk, bk,
    pc, dest, found))

law black_has_move_false_excludes_legal:
  for +fuel: Nat
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for absent: Truth(Bool.not(Retro.black_has_move.go(
    fuel, kind, wk, bk, pc, dest, False{})))
  BlackLegalSegment(fuel, kind, wk, bk, pc,
    dest) -> Empty

law black_has_move_false_if_no_legal:
  for fuel: Nat
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for no_legal: BlackLegalSegment(fuel,
    kind, wk, bk, pc, dest) -> Empty
  Truth(Bool.not(Retro.black_has_move.go(fuel,
    kind, wk, bk, pc, dest, False{})))

law retro_mark_new_preserves_full:
  for +work: Retro.Work
  for +state: Rules.State
  for +rank: U32
  for full: WorkFull(work)
  WorkFull(Retro.mark.new(work, state, rank))

law retro_mark_new_writes_rank:
  for +work: Retro.Work
  for +state: Rules.State
  for +rank: U32
  {WorkWonAt(Retro.mark.new(work, state, rank), state) ==
    rank : U32}

law retro_mark_new_enqueues:
  for +work: Retro.Work
  for +state: Rules.State
  for +rank: U32
  {WorkQueueContents(Retro.mark.new(work, state, rank)) ==
    List.append(&2, Rules.State,
      WorkQueueContents(work), state <> Nil{}) :
    List<&2, Rules.State>}

law retro_mark_new_keeps_other_rank:
  for +work: Retro.Work
  for +state: Rules.State
  for +other: Rules.State
  for +rank: U32
  for full: WorkFull(work)
  for different: {
    ProofTree.bits19(Rules.index(state)) !=
    ProofTree.bits19(Rules.index(other)) : Word(19n)}
  {WorkWonAt(Retro.mark.new(work, state, rank), other) ==
    WorkWonAt(work, other) : U32}

law retro_mark_decision_rank:
  for +work: Retro.Work
  for +state: Rules.State
  for +rank: U32
  for +old: U32
  for decision: Bool
  for observed: {WorkWonAt(work, state) == old : U32}
  {WorkWonAt(Retro.mark.if_decision(
      work, state, rank, decision), state) ==
    Bool.pick(U32, decision, rank, old) : U32}

law retro_mark_rank_value:
  for +work: Retro.Work
  for +state: Rules.State
  for +rank: U32
  {WorkWonAt(Retro.mark.rank(work, state, rank), state) ==
    Bool.pick(U32,
      U32.is_eq(WorkWonAt(work, state), 0),
      rank, WorkWonAt(work, state)) : U32}

law retro_mark_decision_queue:
  for +work: Retro.Work
  for +state: Rules.State
  for +rank: U32
  for decision: Bool
  {WorkQueueContents(Retro.mark.if_decision(
      work, state, rank, decision)) ==
    Bool.pick(List<&2, Rules.State>, decision,
      List.append(&2, Rules.State,
        WorkQueueContents(work), state <> Nil{}),
      WorkQueueContents(work)) : List<&2, Rules.State>}

law retro_mark_rank_queue:
  for +work: Retro.Work
  for +state: Rules.State
  for +rank: U32
  {WorkQueueContents(Retro.mark.rank(work, state, rank)) ==
    Bool.pick(List<&2, Rules.State>,
      U32.is_eq(WorkWonAt(work, state), 0),
      List.append(&2, Rules.State,
        WorkQueueContents(work), state <> Nil{}),
      WorkQueueContents(work)) : List<&2, Rules.State>}

law retro_take_reassembles_queue:
  for +work: Retro.Work
  {WorkTakeReassemble(Retro.take(work)) ==
    WorkQueueContents(work) : List<&2, Rules.State>}

law retro_take_none_means_queue_empty:
  for +work: Retro.Work
  for none: WorkTakeNone(Retro.take(work))
  {WorkQueueContents(work) ==
    Nil{} : List<&2, Rules.State>}

law word_split_append_inverse:
  for n: Nat
  for m: Nat
  for +low: Word(n)
  for +high: Word(m)
  {Encoding.split(m, n,
    Encoding.append(m, n, low, high)) ==
    (low, high) : Word(n) & Word(m)}

law word_and_ones:
  for n: Nat
  for +word: Word(n)
  {Word.and(n, word, Encoding.ones(n)) == word : Word(n)}

law word_and_zero:
  for n: Nat
  for +word: Word(n)
  {Word.and(n, word, Word.zero(n)) ==
    Word.zero(n) : Word(n)}

law word_or_zero:
  for n: Nat
  for +word: Word(n)
  {Word.or(n, word, Word.zero(n)) == word : Word(n)}

law word_zero_or:
  for n: Nat
  for +word: Word(n)
  {Word.or(n, Word.zero(n), word) == word : Word(n)}

law word_or_append:
  for n: Nat
  for m: Nat
  for +a: Word(n)
  for +b: Word(m)
  for +c: Word(n)
  for +d: Word(m)
  {Word.or(Nat.add(n, m),
    Encoding.append(m, n, a, b),
    Encoding.append(m, n, c, d)) ==
    Encoding.append(m, n,
      Word.or(n, a, c), Word.or(m, b, d)) :
    Word(Nat.add(n, m))}

law word_or_disjoint:
  for +n: Nat
  for +m: Nat
  for +low: Word(n)
  for +high: Word(m)
  {Word.or(Nat.add(n, m),
    Encoding.append(m, n, low, Word.zero(m)),
    Encoding.append(m, n, Word.zero(n), high)) ==
    Encoding.append(m, n, low, high) :
    Word(Nat.add(n, m))}

law word_or_into_tail:
  for +n: Nat
  for +m: Nat
  for +low: Word(n)
  for +tail: Word(m)
  for +incoming: Word(m)
  {Word.or(Nat.add(n, m),
    Encoding.append(m, n, low, tail),
    Encoding.append(m, n, Word.zero(n), incoming)) ==
    Encoding.append(m, n, low,
      Word.or(m, tail, incoming)) :
    Word(Nat.add(n, m))}

law word_shr_pad_commutes:
  for n: Nat
  for +word: Word(n)
  {Word.shr(1n+n, Word.shr.pad(n, word)) ==
    Word.shr.pad(n, Word.shr(n, word)) : Word(1n+n)}

law word_shrn_outer_commutes:
  for +size: Nat
  for count: Nat
  for +word: Word(size)
  {Encoding.shrn.outer(size, count, Word.shr(size, word)) ==
    Word.shr(size, Encoding.shrn.outer(size, count, word)) :
    Word(size)}

law word_shrn_inner_equals_outer:
  for +size: Nat
  for count: Nat
  for +word: Word(size)
  {Encoding.shrn.inner(size, count, word) ==
    Encoding.shrn.outer(size, count, word) : Word(size)}

law word_shrn_outer_pad_commutes:
  for +size: Nat
  for count: Nat
  for +word: Word(size)
  {Encoding.shrn.outer(1n+size, count,
      Word.shr.pad(size, word)) ==
    Word.shr.pad(size,
      Encoding.shrn.outer(size, count, word)) :
    Word(1n+size)}

law word_shrn_append_drop:
  for n: Nat
  for +m: Nat
  for +low: Word(n)
  for +high: Word(m)
  {Encoding.shrn.outer(Nat.add(n, m), n,
      Encoding.append(m, n, low, high)) ==
    Encoding.padn(m, n, high) : Word(Nat.add(n, m))}

law word_shrn_inner_append_drop:
  for +n: Nat
  for +m: Nat
  for +low: Word(n)
  for +high: Word(m)
  {Encoding.shrn.inner(Nat.add(n, m), n,
      Encoding.append(m, n, low, high)) ==
    Encoding.padn(m, n, high) : Word(Nat.add(n, m))}

law six_bit_prefix_survives_six_zero_pads:
  for +rest: Word(26n)
  {Encoding.low6(U32{Encoding.padn(26n, 6n, rest)}) ==
    Encoding.low6.of26(Encoding.split(20n, 6n, rest)) :
    Word(6n)}

law six_bit_prefix_survives_twelve_zero_pads:
  for +rest: Word(20n)
  {Encoding.low6(U32{Encoding.padn(20n, 12n, rest)}) ==
    Encoding.low6.of20(Encoding.split(14n, 6n, rest)) :
    Word(6n)}

law eighteen_pads_make_clean_turn:
  for +bit: Bool
  {Encoding.padn(14n, 18n,
      WCon{bit, Word.zero(13n)}) ==
    Encoding.append(18n, 14n,
      WCon{bit, Word.zero(13n)}, Word.zero(18n)) :
    Word(32n)}

law eighteen_pads_make_turn:
  for +bits: Word(14n)
  {Encoding.padn(14n, 18n, bits) ==
    Encoding.append(18n, 14n, bits, Word.zero(18n)) :
    Word(32n)}

law u32_shrn_is_word_inner:
  for count: Nat
  for +word: Word(32n)
  {U32.shrn(U32{word}, count) ==
    U32{Encoding.shrn.inner(32n, count, word)} : U32}

law u32_shrn_drops_six_low_bits:
  for +low: Word(6n)
  for +high: Word(26n)
  {U32.shrn(U32{Encoding.append(26n, 6n, low, high)}, 6n) ==
    U32{Encoding.padn(26n, 6n, high)} : U32}

law u32_shrn_drops_twelve_low_bits:
  for +low: Word(12n)
  for +high: Word(20n)
  {U32.shrn(U32{Encoding.append(20n, 12n, low, high)}, 12n) ==
    U32{Encoding.padn(20n, 12n, high)} : U32}

law u32_shrn_drops_eighteen_low_bits:
  for +low: Word(18n)
  for +high: Word(14n)
  {U32.shrn(U32{Encoding.append(14n, 18n, low, high)}, 18n) ==
    U32{Encoding.padn(14n, 18n, high)} : U32}

law executable_second_square_from_packed_bits:
  for +low: Word(6n)
  for +high: Word(26n)
  {U32.and(U32.shrn(
      U32{Encoding.append(26n, 6n, low, high)}, 6n), 63) ==
    Encoding.square(
      Encoding.low6.of26(
        Encoding.split(20n, 6n, high))) : U32}

law low_six_bits_of_packed_word:
  for +low: Word(6n)
  for +high: Word(26n)
  {Encoding.low6(U32{Encoding.append(26n, 6n,
      low, high)}) == low : Word(6n)}

law second_six_bits_of_nested_word:
  for +bits: Word(6n)
  for +tail: Word(20n)
  {Encoding.low6.of26(Encoding.split(20n, 6n,
      Encoding.append(20n, 6n, bits, tail))) ==
    bits : Word(6n)}

law third_six_bits_of_nested_word:
  for +bits: Word(6n)
  for +tail: Word(14n)
  {Encoding.low6.of20(Encoding.split(14n, 6n,
      Encoding.append(14n, 6n, bits, tail))) ==
    bits : Word(6n)}

law executable_first_square_from_packed_bits:
  for +low: Word(6n)
  for +high: Word(26n)
  {U32.and(U32{Encoding.append(26n, 6n,
      low, high)}, 63) == Encoding.square(low) : U32}

law executable_second_square_from_nested_fields:
  for +wk: Word(6n)
  for +bk: Word(6n)
  for +tail: Word(20n)
  {U32.and(U32.shrn(U32{Encoding.append(26n, 6n, wk,
      Encoding.append(20n, 6n, bk, tail))}, 6n), 63) ==
    Encoding.square(bk) : U32}

law executable_third_square_from_nested_fields:
  for +wk: Word(6n)
  for +bk: Word(6n)
  for +pc: Word(6n)
  for +tail: Word(14n)
  {U32.and(U32.shrn(U32{Encoding.append(26n, 6n, wk,
      Encoding.append(20n, 6n, bk,
        Encoding.append(14n, 6n, pc, tail)))}, 12n), 63) ==
    Encoding.square(pc) : U32}

law executable_turn_from_nested_fields:
  for +wk: Word(6n)
  for +bk: Word(6n)
  for +pc: Word(6n)
  for +side: Bool
  {U32.shrn(U32{Encoding.append(26n, 6n, wk,
      Encoding.append(20n, 6n, bk,
        Encoding.append(14n, 6n, pc,
          WCon{side, Word.zero(13n)})))}, 18n) ==
    Encoding.turn(WCon{side, Word.zero(13n)}) : U32}

law executable_turn_from_any_nested_fields:
  for +wk: Word(6n)
  for +bk: Word(6n)
  for +pc: Word(6n)
  for +high: Word(14n)
  {U32.shrn(U32{Encoding.append(26n, 6n, wk,
      Encoding.append(20n, 6n, bk,
        Encoding.append(14n, 6n, pc, high)))}, 18n) ==
    Encoding.turn(high) : U32}

law executable_third_square_from_packed_bits:
  for +low: Word(12n)
  for +high: Word(20n)
  {U32.and(U32.shrn(
      U32{Encoding.append(20n, 12n, low, high)}, 12n), 63) ==
    Encoding.square(
      Encoding.low6.of20(
        Encoding.split(14n, 6n, high))) : U32}

law executable_turn_from_packed_bits:
  for +low: Word(18n)
  for +side: Bool
  {U32.shrn(U32{Encoding.append(14n, 18n, low,
      WCon{side, Word.zero(13n)})}, 18n) ==
    Encoding.turn(WCon{side, Word.zero(13n)}) : U32}

law executable_turn_from_any_packed_bits:
  for +low: Word(18n)
  for +high: Word(14n)
  {U32.shrn(U32{Encoding.append(14n, 18n, low,
      high)}, 18n) ==
    Encoding.turn(high) : U32}

law regroup_first_two_squares:
  for +wk: Word(6n)
  for +bk: Word(6n)
  for +high: Word(20n)
  {Encoding.append(26n, 6n, wk,
      Encoding.append(20n, 6n, bk, high)) ==
    Encoding.append(20n, 12n,
      Encoding.append(6n, 6n, wk, bk), high) : Word(32n)}

law regroup_first_three_squares:
  for +wk: Word(6n)
  for +bk: Word(6n)
  for +pc: Word(6n)
  for +high: Word(14n)
  {Encoding.append(26n, 6n, wk,
      Encoding.append(20n, 6n, bk,
        Encoding.append(14n, 6n, pc, high))) ==
    Encoding.append(14n, 18n,
      Encoding.append(12n, 6n, wk,
        Encoding.append(6n, 6n, bk, pc)), high) : Word(32n)}

law word_and_append:
  for n: Nat
  for m: Nat
  for +a: Word(n)
  for +b: Word(m)
  for +c: Word(n)
  for +d: Word(m)
  {Word.and(Nat.add(n, m),
    Encoding.append(m, n, a, b),
    Encoding.append(m, n, c, d)) ==
    Encoding.append(m, n,
      Word.and(n, a, c), Word.and(m, b, d)) :
    Word(Nat.add(n, m))}

law structural_six_bit_mask_is_63:
  {Encoding.mask6() == 63 : U32}

law fast_mask_matches_structural_square:
  for +x: U32
  {U32.and(x, 63) ==
    Encoding.square(Encoding.low6(x)) : U32}

law shift_six_square:
  for +bits: Word(6n)
  {U32.shln(Encoding.square(bits), 6n) ==
    U32{Encoding.append(26n, 6n, Word.zero(6n),
      Encoding.append(20n, 6n, bits, Word.zero(20n)))} : U32}

law shift_twelve_square:
  for +bits: Word(6n)
  {U32.shln(Encoding.square(bits), 12n) ==
    U32{Encoding.append(20n, 12n, Word.zero(12n),
      Encoding.append(14n, 6n, bits, Word.zero(14n)))} : U32}

law mask_clean_turn:
  for +bit: Bool
  {U32.and(Encoding.turn(WCon{bit, Word.zero(13n)}), 1) ==
    U32{WCon{bit, Word.zero(31n)}} : U32}

law fast_turn_mask_matches_structural_bit:
  for +turn: U32
  {U32.and(turn, 1) ==
    U32{WCon{Encoding.low1(turn), Word.zero(31n)}} : U32}

law shift_eighteen_bit:
  for +bit: Bool
  {U32.shln(U32{WCon{bit, Word.zero(31n)}}, 18n) ==
    U32{Encoding.append(14n, 18n, Word.zero(18n),
      WCon{bit, Word.zero(13n)})} : U32}

law fast_second_field:
  for +x: U32
  {U32.shln(U32.and(x, 63), 6n) ==
    Encoding.field1(Encoding.low6(x)) : U32}

law fast_third_field:
  for +x: U32
  {U32.shln(U32.and(x, 63), 12n) ==
    Encoding.field2(Encoding.low6(x)) : U32}

law fast_turn_field:
  for +x: U32
  {U32.shln(U32.and(x, 1), 18n) ==
    Encoding.field3(Encoding.low1(x)) : U32}

law merge_first_two_fields:
  for +wk: Word(6n)
  for +bk: Word(6n)
  {U32.or(Encoding.square(wk), Encoding.field1(bk)) ==
    U32{Encoding.append(26n, 6n, wk,
      Encoding.append(20n, 6n, bk, Word.zero(20n)))} : U32}

law merge_first_three_fields:
  for +wk: Word(6n)
  for +bk: Word(6n)
  for +pc: Word(6n)
  {U32.or(U32.or(Encoding.square(wk),
      Encoding.field1(bk)), Encoding.field2(pc)) ==
    U32{Encoding.append(26n, 6n, wk,
      Encoding.append(20n, 6n, bk,
        Encoding.append(14n, 6n, pc,
          Word.zero(14n))))} : U32}

law merge_all_index_fields:
  for +wk: Word(6n)
  for +bk: Word(6n)
  for +pc: Word(6n)
  for +side: Bool
  {U32.or(U32.or(U32.or(
      Encoding.square(wk), Encoding.field1(bk)),
      Encoding.field2(pc)), Encoding.field3(side)) ==
    Encoding.index(Encoding.square(wk),
      Encoding.square(bk), Encoding.square(pc),
      Encoding.turn(WCon{side, Word.zero(13n)})) : U32}

law fast_index_matches_clean_structural:
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +side: U32
  {Rules.index(Rules.State{wk, bk, pc, side}) ==
    Encoding.index(
      Encoding.square(Encoding.low6(wk)),
      Encoding.square(Encoding.low6(bk)),
      Encoding.square(Encoding.low6(pc)),
      Encoding.turn(WCon{Encoding.low1(side),
        Word.zero(13n)})) : U32}

law clean_structural_index_is_index:
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +side: U32
  {Encoding.index(
      Encoding.square(Encoding.low6(wk)),
      Encoding.square(Encoding.low6(bk)),
      Encoding.square(Encoding.low6(pc)),
      Encoding.turn(WCon{Encoding.low1(side),
        Word.zero(13n)})) ==
    Encoding.index(wk, bk, pc, side) : U32}

law executable_index_equals_structural_index:
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +side: U32
  {Rules.index(Rules.State{wk, bk, pc, side}) ==
    Encoding.index(wk, bk, pc, side) : U32}

law executable_decode_clean_index:
  for +wk: Word(6n)
  for +bk: Word(6n)
  for +pc: Word(6n)
  for +side: Bool
  {Rules.decode(Encoding.index(
      Encoding.square(wk), Encoding.square(bk),
      Encoding.square(pc),
      Encoding.turn(WCon{side, Word.zero(13n)}))) ==
    Rules.State{Encoding.square(wk), Encoding.square(bk),
      Encoding.square(pc),
      Encoding.turn(WCon{side, Word.zero(13n)})} : Rules.State}

law executable_decode_packed_fields:
  for +wk: Word(6n)
  for +bk: Word(6n)
  for +pc: Word(6n)
  for +high: Word(14n)
  {Rules.decode(U32{Encoding.append(26n, 6n, wk,
      Encoding.append(20n, 6n, bk,
        Encoding.append(14n, 6n, pc, high)))}) ==
    Rules.State{Encoding.square(wk), Encoding.square(bk),
      Encoding.square(pc), Encoding.turn(high)} : Rules.State}

law structural_decode_packed_fields:
  for +wk: Word(6n)
  for +bk: Word(6n)
  for +pc: Word(6n)
  for +high: Word(14n)
  {Encoding.decode(U32{Encoding.append(26n, 6n, wk,
      Encoding.append(20n, 6n, bk,
        Encoding.append(14n, 6n, pc, high)))}) ==
    (Encoding.square(wk), Encoding.square(bk),
      Encoding.square(pc), Encoding.turn(high)) :
    U32 & U32 & U32 & U32}

law structural_chunks_pack_inverse:
  for +word: Word(32n)
  {Encoding.pack.parts(Encoding.chunks(word)) == word : Word(32n)}

def structural_state.fin(parts: U32 & U32 & U32 & U32) -> Rules.State:
  match parts:
    case (wk, bk, pc, side):
      Rules.State{wk, bk, pc, side}

def structural_state(i: U32) -> Rules.State:
  structural_state.fin(Encoding.decode(i))

law executable_decoder_equals_structural_decoder:
  for +i: U32
  {Rules.decode(i) == structural_state(i) : Rules.State}

law clean_repack_is_low_nineteen_bits:
  for +wk: Word(6n)
  for +bk: Word(6n)
  for +pc: Word(6n)
  for +side: Bool
  for +upper: Word(13n)
  {Encoding.index(Encoding.square(wk), Encoding.square(bk),
      Encoding.square(pc),
      Encoding.turn(WCon{side, upper})) ==
    Encoding.truncate19(U32{Encoding.pack(wk, bk, pc,
      WCon{side, upper})}) : U32}

law executable_repack_of_packed_word_is_low_nineteen_bits:
  for +wk: Word(6n)
  for +bk: Word(6n)
  for +pc: Word(6n)
  for +high: Word(14n)
  {Rules.index(Rules.decode(U32{Encoding.pack(wk, bk, pc,
      high)})) ==
    Encoding.truncate19(U32{Encoding.pack(wk, bk, pc,
      high)}) : U32}

law executable_repack_keeps_low_nineteen_bits:
  for +i: U32
  {Rules.index(Rules.decode(i)) ==
    Encoding.truncate19(i) : U32}

law structural_nineteen_bit_mask_is_524287:
  {Encoding.mask19() == 524287 : U32}

law fast_nineteen_bit_mask_matches_truncation:
  for +i: U32
  {U32.and(i, 524287) == Encoding.truncate19(i) : U32}

law executable_repack_is_nineteen_bit_mask:
  for +i: U32
  {Rules.index(Rules.decode(i)) ==
    U32.and(i, 524287) : U32}

law executable_decode_index_is_canonical:
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +side: U32
  {Rules.decode(Rules.index(
      Rules.State{wk, bk, pc, side})) ==
    Rules.State{
      Encoding.square(Encoding.low6(wk)),
      Encoding.square(Encoding.low6(bk)),
      Encoding.square(Encoding.low6(pc)),
      Encoding.turn(WCon{Encoding.low1(side),
        Word.zero(13n)})} : Rules.State}

law clean_index_is_raw:
  for +wk: Word(6n)
  for +bk: Word(6n)
  for +pc: Word(6n)
  for +side: Bool
  {Encoding.index(Encoding.square(wk),
      Encoding.square(bk), Encoding.square(pc),
      Encoding.turn(WCon{side, Word.zero(13n)})) ==
    U32{Encoding.append(26n, 6n, wk,
      Encoding.append(20n, 6n, bk,
        Encoding.append(14n, 6n, pc,
          WCon{side, Word.zero(13n)})))} : U32}

law word_append_split_inverse:
  for n: Nat
  for +m: Nat
  for +word: Word(Nat.add(n, m))
  {Encoding.join(n, m, Encoding.split(m, n, word)) ==
    word : Word(Nat.add(n, m))}

law structural_index_decode_roundtrip:
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +turn: U32
  {Encoding.decode(Encoding.index(wk, bk, pc, turn)) ==
    (Encoding.square(Encoding.low6(wk)),
      Encoding.square(Encoding.low6(bk)),
      Encoding.square(Encoding.low6(pc)),
      Encoding.turn(WCon{Encoding.low1(turn),
        Word.zero(13n)})) :
    U32 & U32 & U32 & U32}

law structural_square_roundtrip:
  for +bits: Word(6n)
  {Encoding.low6(Encoding.square(bits)) == bits : Word(6n)}

law structural_turn_bit_roundtrip:
  for +bit: Bool
  {Encoding.low1(Encoding.turn(
    WCon{bit, Word.zero(13n)})) == bit : Bool}

def all_zero_bytes(xs: List<&2, U32>) -> Bool:
  List.all(&2, U32, value => U32.is_eq(value, 0), xs)

law uniform_zero_array_serializes_to_zero_values:
  for d: Nat
  Truth(all_zero_bytes(Output.bytes(
    Array.new(U32, d, 0))))

def u32_power_of_two(d: Nat) -> U32:
  match d:
    case 0n:
      1
    case 1n+p:
      U32.shl(u32_power_of_two(p))

def nat_power_of_two(d: Nat) -> Nat:
  match d:
    case 0n:
      1n
    case 1n++p:
      Nat.add(nat_power_of_two(p), nat_power_of_two(p))

law proof_tree_bytes_length:
  for +n: Nat
  for +tree: ProofTree.Tree
  for full: ProofTree.Full(n, tree)
  {List.length(&2, U32,
      ProofTree.bytes(tree)) ==
    nat_power_of_two(n) : Nat}

law proof_tree_byte_at_path:
  for n: Nat
  for +tree: ProofTree.Tree
  for full: ProofTree.Full(n, tree)
  for +bits: Word(n)
  {List.get(&2, U32,
      ProofTree.bytes(tree),
      ProofTree.byte_offset(n,
        bits)) ==
    Some{ProofTree.get(n,
      tree, bits)} : Maybe<&2, U32>}

law uniform_tree_serialized_byte_zero:
  for +n: Nat
  for +bits: Word(n)
  {List.get(&2, U32,
    ProofTree.bytes(
      ProofTree.filled(n,
        0)),
    ProofTree.byte_offset(n,
      bits)) ==
    Some{0} : Maybe<&2, U32>}

law nat_add_associative:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.add(Nat.add(a, b), c) ==
    Nat.add(a, Nat.add(b, c)) : Nat}

law nat_add_right_zero:
  for n: Nat
  {Nat.add(n, 0n) == n : Nat}

law nat_add_succ_right:
  for a: Nat
  for b: Nat
  {Nat.add(a, 1n+b) ==
    1n+Nat.add(a, b) : Nat}

law clock_before_positive_budget:
  for clock: Nat
  for rest: Nat
  Truth(Nat.is_lt(clock,
    Nat.add(clock, 1n+rest)))

law clock_budget_implies_before_hundred:
  for +clock: Nat
  for +rest: Nat
  for budget: {Nat.add(clock,
    1n+rest) == 100n : Nat}
  Truth(Nat.is_lt(clock, 100n))

# A pawn's board-square arithmetic is proved for an arbitrary bounded square.
# Only the six bits of one square are split; no board position is enumerated.
law pawn_rank_after_single_push:
  for +pc: U32
  for bound: Truth(U32.is_lt(pc, 64))
  {Rules.rank(U32.add(pc, 8)) ==
    U32.inc(Rules.rank(pc)) : U32}

law pawn_rank_after_double_push:
  for +pc: U32
  for bound: Truth(U32.is_lt(pc, 64))
  {Rules.rank(U32.add(pc, 16)) ==
    U32.add(Rules.rank(pc), 2) : U32}

law pawn_rank_below_max:
  for +pc: U32
  for bound: Truth(U32.is_lt(pc, 64))
  Truth(U32.is_lt(Rules.rank(pc),
    4294967295))

law pawn_step_increases_rank:
  for +pc: U32
  for +dest: U32
  for +wk: U32
  for +bk: U32
  for +bound: Truth(U32.is_lt(pc, 64))
  for step: Truth(Rules.pawn_step(
    pc, dest, wk, bk))
  Truth(U32.is_lt(Rules.rank(pc),
    Rules.rank(dest)))

law pawn_nat_rank_after_single_push:
  for +pc: U32
  for bound: Truth(U32.is_lt(pc, 64))
  {U32.to_nat(Rules.rank(
      U32.add(pc, 8))) ==
    1n+U32.to_nat(Rules.rank(pc)) : Nat}

law pawn_nat_rank_after_double_push:
  for +pc: U32
  for bound: Truth(U32.is_lt(pc, 64))
  {U32.to_nat(Rules.rank(
      U32.add(pc, 16))) ==
    2n+U32.to_nat(Rules.rank(pc)) : Nat}

law pawn_step_advances_nat_rank:
  for +pc: U32
  for +dest: U32
  for +wk: U32
  for +bk: U32
  for +bound: Truth(U32.is_lt(pc, 64))
  for step: Truth(Rules.pawn_step(
    pc, dest, wk, bk))
  Truth(Nat.is_le(
    1n+U32.to_nat(Rules.rank(pc)),
    U32.to_nat(Rules.rank(dest))))

law pawn_push_preserves_budget:
  for +rest: Nat
  for +pc: U32
  for +dest: U32
  for +wk: U32
  for +bk: U32
  for +bound: Truth(U32.is_lt(pc, 64))
  for step: Truth(Rules.pawn_step(
    pc, dest, wk, bk))
  for invariant: Truth(Nat.is_le(8n,
    Nat.add(1n+rest,
      U32.to_nat(Rules.rank(pc)))))
  Truth(Nat.is_le(8n,
    Nat.add(rest,
      U32.to_nat(Rules.rank(dest)))))

law pawn_rank_positive_nat:
  for +pc: U32
  for +bound: Truth(U32.is_lt(pc, 64))
  for positive: Truth(U32.is_gt(
    Rules.rank(pc), 0))
  Truth(Nat.is_gt(U32.to_nat(
    Rules.rank(pc)), 0n))

law pawn_rank_below_seven_nat:
  for +pc: U32
  for +bound: Truth(U32.is_lt(pc, 64))
  for upper: Truth(U32.is_lt(
    Rules.rank(pc), 7))
  Truth(Nat.is_lt(U32.to_nat(
    Rules.rank(pc)), 7n))

law pawn_valid_rank_bounds:
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +turn: U32
  for valid: Truth(Rules.valid(4,
    Rules.State{wk, bk, pc,
      turn}))
  Truth(U32.is_gt(Rules.rank(pc), 0)) &
  Truth(U32.is_lt(Rules.rank(pc), 7))

law pawn_valid_initial_budget:
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +turn: U32
  for +valid: Truth(Rules.valid(4,
    Rules.State{wk, bk, pc,
      turn}))
  Truth(Nat.is_le(8n,
    Nat.add(7n,
      U32.to_nat(Rules.rank(pc)))))

law pawn_zero_budget_impossible:
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +turn: U32
  for +valid: Truth(Rules.valid(4,
    Rules.State{wk, bk, pc,
      turn}))
  for invariant: Truth(Nat.is_le(8n,
    U32.to_nat(Rules.rank(pc))))
  Empty

law legal_pawn_piece_move_is_push:
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for legal: Truth(Rules.move_to(4,
    Rules.State{wk, bk, pc, 0},
    Rules.State{wk, bk, dest, 1}))
  for changed: Truth(U32.is_ne(pc,
    dest))
  Truth(Rules.pawn_step(pc, dest,
    wk, bk))

law legal_pawn_piece_move_changes_square:
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for legal: Truth(Rules.move_to(4,
    Rules.State{wk, bk, pc, 0},
    Rules.State{wk, bk, dest, 1}))
  Truth(U32.is_ne(pc, dest))

law legal_pawn_piece_move_resets_clock:
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for legal: Truth(Rules.move_to(4,
    Rules.State{wk, bk, pc, 0},
    Rules.State{wk, bk, dest, 1}))
  Truth(U32.is_eq(4, 4) &&
    U32.is_ne(pc, dest))

law legal_pawn_push_preserves_budget:
  for +rest: Nat
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for +legal: Truth(Rules.move_to(4,
    Rules.State{wk, bk, pc, 0},
    Rules.State{wk, bk, dest, 1}))
  for changed: Truth(U32.is_ne(pc,
    dest))
  for invariant: Truth(Nat.is_le(8n,
    Nat.add(1n+rest,
      U32.to_nat(Rules.rank(pc)))))
  Truth(Nat.is_le(8n,
    Nat.add(rest,
      U32.to_nat(Rules.rank(dest)))))

law uniform_array_serialized_length:
  for +d: Nat
  for +value: U32
  {List.length(&2, U32, Output.bytes(
    Array.new(U32, d, value))) ==
    nat_power_of_two(d) : Nat}

law three_man_slot_count:
  {u32_power_of_two(19n) == 524288 : U32}

law uniform_array_size:
  for d: Nat
  for +value: U32
  {Array.size(U32, Array.new(U32, d, value)) ==
    (Array.new(U32, d, value), u32_power_of_two(d)) :
    Array<U32> & U32}

law uniform_array_get_go:
  for d: Nat
  for +value: U32
  for +n: U32
  for +i: U32
  {array_value(Array.get.go(U32,
    Array.new(U32, d, value), n, i)) == value : U32}

law uniform_array_get:
  for +d: Nat
  for +value: U32
  for +i: U32
  {array_value(Array.get(U32,
    Array.new(U32, d, value), i)) == value : U32}

def StateInRange(s: Rules.State) -> Type:
  match s:
    case Rules.State{wk, bk, pc, turn}:
      Truth(U32.is_lt(wk, 64)) &
      Truth(U32.is_lt(bk, 64)) &
      Truth(U32.is_lt(pc, 64))

law u32_equality_reflexive:
  for +x: U32
  Truth(U32.is_eq(x, x))

law u32_equality_reflects_identity:
  for +x: U32
  for +y: U32
  Truth(U32.is_eq(x, y)) -> {x == y : U32}

law same_class_white_move_is_a_game_move:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +wk2: U32
  for +bk2: U32
  for +pc2: U32
  Truth(Rules.move_to(kind, Rules.State{wk, bk, pc, 0},
    Rules.State{wk2, bk2, pc2, 1})) ->
    WDL.Truth(WDL.move(WDL.White{kind, wk, bk, pc},
      WDL.Black{kind, wk2, bk2, pc2}))

law game_move_with_same_white_material_is_a_rules_move:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +wk2: U32
  for +bk2: U32
  for +pc2: U32
  WDL.Truth(WDL.move(WDL.White{kind, wk, bk, pc},
    WDL.Black{kind, wk2, bk2, pc2})) ->
    Truth(Rules.move_to(kind, Rules.State{wk, bk, pc, 0},
      Rules.State{wk2, bk2, pc2, 1}))

law same_class_black_move_is_a_game_move:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +wk2: U32
  for +bk2: U32
  for +pc2: U32
  Truth(Rules.move_to(kind, Rules.State{wk, bk, pc, 1},
    Rules.State{wk2, bk2, pc2, 0})) ->
    WDL.Truth(WDL.move(WDL.Black{kind, wk, bk, pc},
      WDL.White{kind, wk2, bk2, pc2}))

law game_move_with_same_black_material_is_a_rules_move:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +wk2: U32
  for +bk2: U32
  for +pc2: U32
  WDL.Truth(WDL.move(WDL.Black{kind, wk, bk, pc},
    WDL.White{kind, wk2, bk2, pc2})) ->
    Truth(Rules.move_to(kind, Rules.State{wk, bk, pc, 1},
      Rules.State{wk2, bk2, pc2, 0}))

law legal_quiet_black_destination_is_a_rules_move:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for valid: Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, 1}))
  for +legal: Truth(Rules.black_move(kind, wk, bk, pc,
    dest))
  for quiet: Truth(Bool.not(U32.is_eq(dest, pc)))
  Truth(Rules.move_to(kind,
    Rules.State{wk, bk, pc, 1},
    Rules.State{wk, dest, pc, 0}))

law black_rules_move_is_a_legal_destination:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for +move: Truth(Rules.move_to(kind,
    Rules.State{wk, bk, pc, 1},
    Rules.State{wk, dest, pc, 0}))
  Truth(Rules.black_move(kind, wk, bk, pc, dest))

law legal_black_capture_is_a_draw_exit:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for valid: Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, 1}))
  Truth(Rules.black_move(kind, wk, bk, pc, pc)) ->
    WDL.Truth(WDL.move(WDL.Black{kind, wk, bk, pc},
      WDL.KingsOnly{}))

law game_draw_exit_is_a_legal_black_capture:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  WDL.Truth(WDL.move(WDL.Black{kind, wk, bk, pc},
    WDL.KingsOnly{})) ->
    Truth(Rules.valid(kind, Rules.State{wk, bk, pc, 1})) &
    Truth(Rules.black_move(kind, wk, bk, pc, pc))

law semantic_promotion_has_seed_shape:
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +kind: U32
  for +wk2: U32
  for +bk2: U32
  for +pc2: U32
  WDL.Truth(WDL.promotion(wk, bk, pc,
    kind, wk2, bk2, pc2)) ->
    Truth(Rules.pawn_can_promote(wk, bk, pc))

law legal_pawn_seed_has_semantic_promotion:
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +kind: U32
  for can: Truth(Rules.pawn_can_promote(wk, bk, pc))
  for bound: Truth(U32.is_lt(kind, 4))
  for target_valid: Truth(Rules.valid(kind,
    Rules.State{wk, bk, (pc + 8 : U32), 1}))
  WDL.Truth(WDL.promotion(wk, bk, pc,
    kind, wk, bk, (pc + 8 : U32)))

law pawn_queen_or_rook_promotion_is_game_move:
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +kind: U32
  for +wk2: U32
  for +bk2: U32
  for +pc2: U32
  for bound: Truth(U32.is_lt(kind, 2))
  WDL.Truth(WDL.promotion(wk, bk, pc,
    kind, wk2, bk2, pc2)) ->
    WDL.Truth(WDL.move(WDL.White{4, wk, bk, pc},
      WDL.Black{kind, wk2, bk2, pc2}))

law game_move_to_queen_or_rook_is_promotion:
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +kind: U32
  for +wk2: U32
  for +bk2: U32
  for +pc2: U32
  for bound: Truth(U32.is_lt(kind, 2))
  WDL.Truth(WDL.move(WDL.White{4, wk, bk, pc},
    WDL.Black{kind, wk2, bk2, pc2})) ->
    WDL.Truth(WDL.promotion(wk, bk, pc,
      kind, wk2, bk2, pc2))

law bishop_promotion_is_draw_exit:
  for +wk: U32
  for +bk: U32
  for +pc: U32
  WDL.Truth(WDL.promotion(wk, bk, pc, 2,
    wk, bk, (pc + 8 : U32))) ->
    WDL.Truth(WDL.move(WDL.White{4, wk, bk, pc},
      WDL.BareBishop{}))

law knight_promotion_is_draw_exit:
  for +wk: U32
  for +bk: U32
  for +pc: U32
  WDL.Truth(WDL.promotion(wk, bk, pc, 3,
    wk, bk, (pc + 8 : U32))) ->
    WDL.Truth(WDL.move(WDL.White{4, wk, bk, pc},
      WDL.BareKnight{}))

law white_same_class_move_changes_king_or_piece:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +wk2: U32
  for +bk2: U32
  for +pc2: U32
  for legal: Truth(Rules.move_to(kind,
    Rules.State{wk, bk, pc, 0},
    Rules.State{wk2, bk2, pc2, 1}))
  for same_king: Truth(U32.is_eq(wk, wk2))
  Truth(U32.is_eq(pc, pc2)) -> Empty

# A legal black king move cannot put the kings next to each other.
law black_king_stays_separated:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for legal: Truth(Rules.black_move(kind, wk, bk, pc, dest))
  Truth(Bool.not(Position.kings_touch(wk, dest)))

law every_white_move_has_reverse_search_shape:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +wk2: U32
  for +bk2: U32
  for +pc2: U32
  Truth(Rules.move_to(kind, Rules.State{wk, bk, pc, 0},
    Rules.State{wk2, bk2, pc2, 1})) ->
    Truth(U32.is_eq(bk, bk2) &&
      (U32.is_eq(pc, pc2) || U32.is_eq(wk, wk2)))

law every_black_move_has_reverse_search_shape:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +wk2: U32
  for +bk2: U32
  for +pc2: U32
  Truth(Rules.move_to(kind, Rules.State{wk, bk, pc, 1},
    Rules.State{wk2, bk2, pc2, 0})) ->
    Truth(U32.is_eq(wk, wk2) && U32.is_eq(pc, pc2))

law legal_three_man_position_has_no_black_king_check:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +turn: U32
  Truth(Rules.valid(kind, Rules.State{wk, bk, pc, turn})) ->
    Truth(Bool.not(Position.kings_touch(wk, bk)))

law lone_black_king_cannot_checkmate:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +turn: U32
  for valid: Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, turn}))
  Truth(Position.kings_touch(wk, bk)) -> Empty

law white_mate_is_impossible:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  WDL.WhiteMate(kind, wk, bk, pc) -> Empty

law black_cannot_force_win:
  for n: Nat
  for +game: WDL.Game
  WDL.BlackWinWithin(n, game) -> Empty

law black_cannot_force_clocked_win:
  for n: Nat
  for clock: Nat
  for +game: WDL.Game
  Clocked.BlackWinWithin(n, clock, game) -> Empty

law bare_kings_are_terminal_draw:
  Clocked.DrawAtClockZero(WDL.KingsOnly{})

law bishop_material_is_terminal_draw:
  for +turn: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  Clocked.DrawAtClockZero(WDL.material_game(2, turn, wk, bk, pc))

law knight_material_is_terminal_draw:
  for +turn: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  Clocked.DrawAtClockZero(WDL.material_game(3, turn, wk, bk, pc))

law bishop_zero_array_entry_is_correct:
  for +d: Nat
  for +turn: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  {array_value(Array.get(U32,
    Array.new(U32, d, 0),
    Rules.index(Rules.State{wk, bk, pc, turn}))) == 0 : U32} &
  Clocked.DrawAtClockZero(WDL.material_game(2, turn, wk, bk, pc))

law knight_zero_array_entry_is_correct:
  for +d: Nat
  for +turn: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  {array_value(Array.get(U32,
    Array.new(U32, d, 0),
    Rules.index(Rules.State{wk, bk, pc, turn}))) == 0 : U32} &
  Clocked.DrawAtClockZero(WDL.material_game(3, turn, wk, bk, pc))

law legal_state_squares_are_in_reverse_search_range:
  for +kind: U32
  for +s: Rules.State
  Truth(Rules.valid(kind, s)) -> StateInRange(s)

law legal_black_move_destination_in_range:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for valid: Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, 1}))
  for move: Truth(Rules.black_move(kind, wk, bk, pc, dest))
  Truth(U32.is_lt(dest, 64))

law work_black_reply_scan_covers_legal_move:
  for +work: Retro.Work
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for complete: WorkSquaresComplete(work)
  for valid: Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, 1}))
  for +move: Truth(Rules.black_move(kind, wk, bk, pc, dest))
  for all: Truth(BlackScanAll(Retro.black_reply_scan(
    kind, Rules.State{wk, bk, pc, 1},
    WorkWonTree(work), WorkSquares(work))))
  Truth(Bool.not(U32.is_eq(dest, pc))) &
  Truth(U32.is_ne(ProofTree.get_index(
    WorkWonTree(work), Rules.index(
      Rules.State{wk, dest, pc, 0})), 0))

law work_black_reply_scan_sees_legal_move:
  for +work: Retro.Work
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for complete: WorkSquaresComplete(work)
  for valid: Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, 1}))
  for +move: Truth(Rules.black_move(kind, wk, bk, pc, dest))
  Truth(BlackScanSeen(Retro.black_reply_scan(
    kind, Rules.State{wk, bk, pc, 1},
    WorkWonTree(work), WorkSquares(work))))

law work_black_has_move_detects_legal_move:
  for +work: Retro.Work
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +dest: U32
  for complete: WorkSquaresComplete(work)
  for valid: Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, 1}))
  for +move: Truth(Rules.black_move(kind, wk, bk, pc, dest))
  Truth(Retro.black_has_move(kind,
    Rules.State{wk, bk, pc, 1}, WorkSquares(work)))

# This theorem quantifies over an arbitrary successor list; it does not
# enumerate board positions. It captures the all-successors condition for a
# Black-to-move position in retrograde propagation.
law zero_remaining_means_all_winning:
  for xs: List<&2, Bool>
  for zero: Truth(Nat.is_eq(Logic.unresolved(xs), 0n))
  Truth(Logic.all_winning(xs))

law all_winning_means_zero_remaining:
  for xs: List<&2, Bool>
  for all: Truth(Logic.all_winning(xs))
  Truth(Nat.is_eq(Logic.unresolved(xs), 0n))

# Resolving one previously unresolved successor removes exactly one unit from
# the abstract remaining count, regardless of the surrounding successors.
law resolving_one_decrements_remaining:
  for +before: List<&2, Bool>
  for +after: List<&2, Bool>
  {Logic.unresolved(Logic.join(before, False{} <> after)) ==
    1n+Logic.unresolved(Logic.join(before, True{} <> after)) : Nat}

# A permanent draw exit, such as capture into K vs K, prevents Black's
# remaining count from reaching zero.
law draw_exit_keeps_black_unresolved:
  for before: List<&2, Bool>
  for after: List<&2, Bool>
  Truth(Bool.not(Nat.is_eq(
    Logic.unresolved(Logic.join(before, False{} <> after)), 0n)))

law resolving_one_only_adds_wins:
  for +before: List<&2, Bool>
  for +after: List<&2, Bool>
  Truth(Logic.extends(
    Logic.join(before, False{} <> after),
    Logic.join(before, True{} <> after)))

law extension_reflexive:
  for +xs: List<&2, Bool>
  Truth(Logic.extends(xs, xs))

# Both player clauses of the retrograde attractor are monotone: learning more
# winning successors cannot revoke an already established win.
law white_attractor_monotone:
  for +old: List<&2, Bool>
  for +new: List<&2, Bool>
  for extension: Truth(Logic.extends(old, new))
  for prior: Truth(Logic.any_winning(old))
  Truth(Logic.any_winning(new))

law black_attractor_monotone:
  for +old: List<&2, Bool>
  for +new: List<&2, Bool>
  for extension: Truth(Logic.extends(old, new))
  for prior: Truth(Logic.all_winning(old))
  Truth(Logic.all_winning(new))

law black_loss_monotone:
  for +check: Bool
  for +old: List<&2, Bool>
  for +new: List<&2, Bool>
  for extension: Truth(Logic.extends(old, new))
  for prior: Truth(Logic.black_forced_loss(check, old))
  Truth(Logic.black_forced_loss(check, new))

# The K vs K capture exit is never a White win at any finite horizon.
law bare_kings_never_win:
  for n: Nat
  WDL.WinWithin(n, WDL.KingsOnly{}) -> Empty

# Giving White another ply cannot destroy an existing forced-win strategy.
law winning_horizon_monotone:
  for n: Nat
  for +game: WDL.Game
  WDL.WinWithin(n, game) -> WDL.WinWithin(1n+n, game)

law bare_kings_are_not_white_win:
  WDL.WhiteCanForceWin(WDL.KingsOnly{}) -> Empty

law capture_exit_refutes_white_win:
  for n: Nat
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for capture: WDL.Truth(WDL.move(
    WDL.Black{kind, wk, bk, pc}, WDL.KingsOnly{}))
  for not_mate: WDL.BlackMate(kind, wk, bk, pc) -> Empty
  WDL.WinWithin(n, WDL.Black{kind, wk, bk, pc}) -> Empty

law legal_capture_is_not_checkmate:
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for capture: WDL.Truth(WDL.move(
    WDL.Black{kind, wk, bk, pc}, WDL.KingsOnly{}))
  WDL.BlackMate(kind, wk, bk, pc) -> Empty

law legal_capture_refutes_white_win:
  for n: Nat
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for +capture: WDL.Truth(WDL.move(
    WDL.Black{kind, wk, bk, pc}, WDL.KingsOnly{}))
  WDL.WinWithin(n, WDL.Black{kind, wk, bk, pc}) -> Empty

# Any set closed under the one-ply attractor contains every finite-horizon
# White win. This is the symbolic completeness half of retrograde analysis.
law closed_set_contains_forced_wins:
  for ~P: WDL.Game -> Type
  for ~close: @game: WDL.Game -> WDL.Attractor(~P, game) -> P(game)
  for n: Nat
  for +game: WDL.Game
  WDL.WinWithin(n, game) -> P(game)

law fifty_move_draw_on_white_turn:
  for n: Nat
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  Clocked.WinWithin(n, 100n, WDL.White{kind, wk, bk, pc}) -> Empty

law fifty_move_draw_on_black_turn_unless_mate:
  for n: Nat
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for no_mate: WDL.BlackMate(kind, wk, bk, pc) -> Empty
  Clocked.WinWithin(n, 100n, WDL.Black{kind, wk, bk, pc}) -> Empty

law checkmate_is_terminal_win:
  for clock: Nat
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  WDL.BlackMate(kind, wk, bk, pc) ->
    Clocked.WinWithin(0n, clock, WDL.Black{kind, wk, bk, pc})

law stalemate_is_not_white_win:
  for n: Nat
  for clock: Nat
  for +kind: U32
  for +wk: U32
  for +bk: U32
  for +pc: U32
  for no_move: WDL.BlackHasMove(kind, wk, bk, pc) -> Empty
  for no_mate: WDL.BlackMate(kind, wk, bk, pc) -> Empty
  Clocked.WinWithin(n, clock, WDL.Black{kind, wk, bk, pc}) -> Empty

law bare_bishop_is_not_white_win:
  for n: Nat
  for clock: Nat
  Clocked.WinWithin(n, clock, WDL.BareBishop{}) -> Empty

law bare_knight_is_not_white_win:
  for n: Nat
  for clock: Nat
  Clocked.WinWithin(n, clock, WDL.BareKnight{}) -> Empty

law closed_clocked_set_contains_forced_wins:
  for ~P: Clocked.Timed -> Type
  for ~close: @timed: Clocked.Timed ->
    Clocked.Attractor(~P, timed) -> P(timed)
  for n: Nat
  for +clock: Nat
  for +game: WDL.Game
  Clocked.WinWithin(n, clock, game) ->
    P(Clocked.Timed{clock, game})

law safe_unclocked_win_survives_fifty_move_rule:
  for n: Nat
  for +clock: Nat
  for +game: WDL.Game
  for safe: Clocked.Safe(n, clock)
  WDL.WinWithin(n, game) -> Clocked.WinWithin(n, clock, game)

# A symbolic rank certificate is sound: the local decrease obligations imply
# a forced win within the stated horizon. No board positions are enumerated.
law bounded_rank_certificate_is_sound:
  for ~rank: WDL.Game -> Nat
  for ~cert: Ranked.BoundedCertificate(~rank)
  for +n: Nat
  for +game: WDL.Game
  Ranked.PositiveAtMost(~rank, n, game) -> WDL.WinWithin(n, game)

law local_rank_certificate_implies_bounded:
  for ~rank: WDL.Game -> Nat
  for ~local: Ranked.LocalCertificate(~rank)
  Ranked.BoundedCertificate(~rank)

law local_rank_certificate_is_sound:
  for ~rank: WDL.Game -> Nat
  for ~local: Ranked.LocalCertificate(~rank)
  for +game: WDL.Game
  WDL.Truth(Nat.is_gt(rank(game), 0n)) ->
    WDL.WhiteCanForceWin(game)

law local_rank_certificate_wins_at_its_rank:
  for ~rank: WDL.Game -> Nat
  for ~local: Ranked.LocalCertificate(~rank)
  for +game: WDL.Game
  WDL.Truth(Nat.is_gt(rank(game), 0n)) ->
    WDL.WinWithin(rank(game), game)

law local_rank_certificate_is_clock_zero_sound:
  for ~rank: WDL.Game -> Nat
  for ~local: Ranked.LocalCertificate(~rank)
  for +game: WDL.Game
  for positive: WDL.Truth(Nat.is_gt(rank(game), 0n))
  for safe: Clocked.Safe(rank(game), 0n)
  Clocked.ClockZeroWhiteWin(game)

law zero_rank_closure_is_complete:
  for ~rank: WDL.Game -> Nat
  for ~zero: Ranked.ZeroCertificate(~rank)
  for n: Nat
  for +game: WDL.Game
  WDL.WinWithin(n, game) -> Ranked.Positive(~rank, game)

law zero_local_certificate_implies_closure:
  for ~rank: WDL.Game -> Nat
  for ~local_zero: Ranked.ZeroLocalCertificate(~rank)
  Ranked.ZeroCertificate(~rank)

law clocked_win_implies_unclocked_win:
  for n: Nat
  for +clock: Nat
  for +game: WDL.Game
  Clocked.WinWithin(n, clock, game) -> WDL.WinWithin(n, game)

law zero_local_rank_refutes_clocked_win:
  for ~rank: WDL.Game -> Nat
  for ~local_zero: Ranked.ZeroLocalCertificate(~rank)
  for +n: Nat
  for +clock: Nat
  for +game: WDL.Game
  for zero: WDL.Truth(Nat.is_eq(rank(game), 0n))
  Clocked.WinWithin(n, clock, game) -> Empty

# A purely arithmetic bridge: fewer than 100 remaining plies imply the
# structural safety budget for every possible combination of clock increments
# and zeroing resets. It does not quantify over, or enumerate, chess boards.
law plies_below_fifty_move_limit_are_safe:
  for n: Nat
  for +clock: Nat
  WDL.Truth(Nat.is_le(Nat.add(n, clock), 99n)) ->
    Clocked.Safe(n, clock)

law bounded_rank_is_clock_zero_win:
  for ~rank: WDL.Game -> Nat
  for ~local: Ranked.LocalCertificate(~rank)
  for +game: WDL.Game
  for positive: Ranked.Positive(~rank, game)
  for bound: WDL.Truth(Nat.is_le(rank(game), 99n))
  Clocked.ClockZeroWhiteWin(game)

law phase_rank_fits_fifty_move_limit:
  for pawn: Bool
  for raw: Nat
  WDL.Truth(Nat.is_le(raw, 49n)) ->
    WDL.Truth(Nat.is_le(Ranked.phase_rank(pawn, raw), 99n))

law promotion_decreases_phase_rank:
  for pawn_raw: Nat
  for +promoted_raw: Nat
  for positive: WDL.Truth(Nat.is_gt(pawn_raw, 0n))
  for promoted_bound: WDL.Truth(Nat.is_le(promoted_raw, 49n))
  WDL.Truth(Nat.is_lt(promoted_raw,
    Ranked.phase_rank(True{}, pawn_raw)))

law lifted_rank_fits_fifty_move_limit:
  for ~raw: WDL.Game -> Nat
  for +game: WDL.Game
  WDL.Truth(Nat.is_le(raw(game), 49n)) ->
    WDL.Truth(Nat.is_le(Ranked.lifted_rank(~raw, game), 99n))

law lifted_rank_certificate_is_clock_zero_sound:
  for ~raw: WDL.Game -> Nat
  for ~local: Ranked.LocalCertificate(~Ranked.lifted_rank(~raw))
  for +game: WDL.Game
  for positive: Ranked.Positive(~Ranked.lifted_rank(~raw), game)
  for raw_bound: WDL.Truth(Nat.is_le(raw(game), 49n))
  Clocked.ClockZeroWhiteWin(game)

law local_certificates_give_exact_clock_zero_wdl:
  for ~rank: WDL.Game -> Nat
  for ~wins: Ranked.LocalCertificate(~rank)
  for ~draws: Ranked.ZeroLocalCertificate(~rank)
  for +game: WDL.Game
  for bound: WDL.Truth(Nat.is_le(rank(game), 99n))
  Ranked.ExactClockZero(~rank, game)
