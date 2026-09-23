import Base
import ./LAWS.bend as Laws
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
import ./src/clocked_tables.bend as ClockedTables
import ./src/clocked_index.bend as ClockedIndex
import ./src/path_tree.bend as PathTree
import ./src/minimax_spec.bend as Minimax
import ./src/exact_spec.bend as Exact
import ./src/pawn_arithmetic.bend as PawnArithmetic
import ./src/resource_wdl_spec.bend as Resource

def path_prepend_preserves_full(n: Nat,
  +word_len: Nat, +bit: Bool,
  tree: PathTree.Tree<Word(word_len)>,
  full: PathTree.Full(n,
    Word(word_len), tree)) ->
  PathTree.Full(n,
    Word(1n+word_len),
    PathTree.prepend(word_len, bit,
      tree)):
  match n tree full:
    case 0n PathTree.Leaf{word} proof:
      Unit{}
    case 0n PathTree.Node{left, right}
         impossible:
      impossible
    case 1n++rest PathTree.Leaf{word}
         impossible:
      impossible
    case 1n++rest PathTree.Node{left, right}
         pair:
      match pair:
        case (left_full, right_full):
          (path_prepend_preserves_full(
             rest, word_len, bit, left,
             left_full),
           path_prepend_preserves_full(
             rest, word_len, bit, right,
             right_full))

def Laws.canonical_paths_are_full(n):
  match n:
    case 0n:
      Unit{}
    case 1n++rest:
      (path_prepend_preserves_full(
         rest, rest, False{},
         PathTree.paths(rest),
         Laws.canonical_paths_are_full(
           rest)),
       path_prepend_preserves_full(
         rest, rest, True{},
         PathTree.paths(rest),
         Laws.canonical_paths_are_full(
           rest)))

def Laws.path_tabulation_is_full(
  n, paths, full, kind, clock,
  squares, next, reset, queen,
  rook):
  match n paths full:
    case 0n PathTree.Leaf{path} proof:
      Unit{}
    case 0n PathTree.Node{left, right}
         impossible:
      impossible
    case 1n++rest PathTree.Leaf{path}
         impossible:
      impossible
    case 1n++rest PathTree.Node{left, right}
         pair:
      match pair:
        case (left_full, right_full):
          (Laws.path_tabulation_is_full(
             rest, left, left_full,
             kind, clock, squares,
             next, reset, queen,
             rook),
           Laws.path_tabulation_is_full(
             rest, right, right_full,
             kind, clock, squares,
             next, reset, queen,
             rook))

def Laws.zero_path_tabulation_is_full(
  n, paths, full):
  match n paths full:
    case 0n PathTree.Leaf{path} proof:
      Unit{}
    case 0n PathTree.Node{left, right}
         impossible:
      impossible
    case 1n+rest PathTree.Leaf{path}
         impossible:
      impossible
    case 1n++rest PathTree.Node{left,
         right} pair:
      match pair:
        case (left_full, right_full):
          (Laws.zero_path_tabulation_is_full(
             rest, left, left_full),
           Laws.zero_path_tabulation_is_full(
             rest, right,
             right_full))

def Laws.nonpawn_go_is_full(
  remaining, clock, kind, squares,
  paths, full, zero):
  match remaining:
    case 0n:
      Laws.path_tabulation_is_full(
        19n, paths, full,
        kind, clock, squares,
        zero, zero, zero, zero)
    case 1n+rest:
      Laws.path_tabulation_is_full(
        19n, paths, full,
        kind, clock, squares,
        ClockedTables.nonpawn.go(
          rest, 1n+clock, kind,
          squares, paths, zero),
        zero, zero, zero)

def Laws.pawn_clock_go_is_full(
  remaining, clock, squares,
  paths, full, reset, queen,
  rook, zero):
  match remaining:
    case 0n:
      Laws.path_tabulation_is_full(
        19n, paths, full,
        4, clock, squares,
        zero, reset, queen, rook)
    case 1n+rest:
      Laws.path_tabulation_is_full(
        19n, paths, full,
        4, clock, squares,
        ClockedTables.pawn.clock.go(
          rest, 1n+clock, squares,
          paths, reset, queen,
          rook, zero),
        reset, queen, rook)

def Laws.pawn_budget_go_is_full(
  pushes, squares, paths, full,
  queen, rook, zero):
  match pushes:
    case 0n:
      Laws.zero_path_tabulation_is_full(
        19n, paths, full)
    case 1n+rest:
      Laws.pawn_clock_go_is_full(
        100n, 0n, squares,
        paths, full,
        ClockedTables.pawn.budget.go(
          rest, squares, paths,
          queen, rook, zero),
        queen, rook, zero)

def Laws.minimax_has_move_matches_executable_scan(
  candidates, kind, wk, bk, pc, found):
  match candidates:
    case Nil{}:
      {==}
    case dest <> tail:
      Laws.minimax_has_move_matches_executable_scan(
        tail, kind, wk, bk, pc,
        found || Rules.black_move(kind,
          wk, bk, pc, dest))

def Laws.minimax_path_correct_lookup(
  depth, fuel, clock, kind, squares,
  paths, table, cert, bits):
  match depth paths table cert bits:
    case 0n PathTree.Leaf{path}
         ProofTree.Leaf{value} proof WNil{}:
      proof
    case 1n+rest PathTree.Leaf{path}
         ProofTree.Leaf{value} proof
         WCon{bit, tail}:
      proof
    case 0n PathTree.Node{left, right}
         ProofTree.Node{table_left, table_right}
         Laws.Both{left_cert, right_cert}
         WNil{}:
      Laws.minimax_path_correct_lookup(0n,
        fuel, clock, kind, squares, left,
        table_left, left_cert, WNil{})
    case 1n+rest PathTree.Node{left, right}
         ProofTree.Node{table_left, table_right}
         Laws.Both{left_cert, right_cert}
         WCon{False{}, tail}:
      Laws.minimax_path_correct_lookup(rest,
        fuel, clock, kind, squares, left,
        table_left, left_cert, tail)
    case 1n+rest PathTree.Node{left, right}
         ProofTree.Node{table_left, table_right}
         Laws.Both{left_cert, right_cert}
         WCon{True{}, tail}:
      Laws.minimax_path_correct_lookup(rest,
        fuel, clock, kind, squares, right,
        table_right, right_cert, tail)
    case _ PathTree.Leaf{path}
         ProofTree.Node{left, right}
         impossible _:
      match impossible:
    case _ PathTree.Node{left, right}
         ProofTree.Leaf{value}
         impossible _:
      match impossible:

def Laws.exact_pawn_path_correct_lookup(
  depth, pushes, remaining, squares,
  paths, table, cert, bits):
  match depth paths table cert bits:
    case 0n PathTree.Leaf{path}
         ProofTree.Leaf{value} proof WNil{}:
      proof
    case 1n+rest PathTree.Leaf{path}
         ProofTree.Leaf{value} proof
         WCon{bit, tail}:
      proof
    case 0n PathTree.Node{left, right}
         ProofTree.Node{table_left, table_right}
         Laws.Both{left_cert, right_cert}
         WNil{}:
      Laws.exact_pawn_path_correct_lookup(
        0n, pushes, remaining, squares,
        left, table_left, left_cert,
        WNil{})
    case 1n+rest PathTree.Node{left, right}
         ProofTree.Node{table_left, table_right}
         Laws.Both{left_cert, right_cert}
         WCon{False{}, tail}:
      Laws.exact_pawn_path_correct_lookup(
        rest, pushes, remaining,
        squares, left, table_left,
        left_cert, tail)
    case 1n+rest PathTree.Node{left, right}
         ProofTree.Node{table_left, table_right}
         Laws.Both{left_cert, right_cert}
         WCon{True{}, tail}:
      Laws.exact_pawn_path_correct_lookup(
        rest, pushes, remaining,
        squares, right, table_right,
        right_cert, tail)
    case _ PathTree.Leaf{path}
         ProofTree.Node{left, right}
         impossible _:
      match impossible:
    case _ PathTree.Node{left, right}
         ProofTree.Leaf{value}
         impossible _:
      match impossible:

def and_left(+a: Bool, -b: Bool, proof: Laws.Truth(a && b)) ->
  Laws.Truth(a):
  match a:
    case True{}:
      Unit{}
    case False{}:
      Empty.absurd(Laws.Truth(False{}), proof)

def and_right(+a: Bool, -b: Bool, proof: Laws.Truth(a && b)) ->
  Laws.Truth(b):
  match a:
    case True{}:
      proof
    case False{}:
      Empty.absurd(Laws.Truth(b), proof)

def pair_left(-A: Type, -B: Type, pair: A & B) -> A:
  match pair:
    case (left, right):
      left

def pair_right(-A: Type, -B: Type, pair: A & B) -> B:
  match pair:
    case (left, right):
      right

def and_intro(+a: Bool, +b: Bool,
  left: Laws.Truth(a), right: Laws.Truth(b)) ->
  Laws.Truth(a && b):
  match a:
    case True{}:
      right
    case False{}:
      left

def truth_and_split(+a: Bool, +b: Bool,
  +yes: Laws.Truth(a && b)) ->
  Laws.Truth(a) & Laws.Truth(b):
  (and_left(a, b, yes),
   and_right(a, b, yes))

def bool_and_assoc(+a: Bool, +b: Bool,
  +c: Bool) ->
  {a && (b && c) == (a && b) && c : Bool}:
  match a b c:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def bool_pick_ne_zero_is_bool(value: Bool) ->
  {U32.is_ne(Bool.pick(U32, value,
    1, 0), 0) == value : Bool}:
  match value:
    case True{}:
      {==}
    case False{}:
      {==}

def guarded_or_cong(+guard: Bool,
  +left: Bool, +right: Bool,
  +tail_left: Bool, +tail_right: Bool,
  head: Laws.Truth(guard) ->
    {left == right : Bool},
  tail: {tail_left == tail_right : Bool}) ->
  {(guard && left) || tail_left ==
    (guard && right) || tail_right : Bool}:
  match guard:
    case False{}:
      tail
    case True{}:
      Equal.trans(Bool,
        left || tail_left,
        right || tail_left,
        right || tail_right,
        Equal.cong(Bool, Bool,
          value => value || tail_left,
          left, right, head(Unit{})),
        Equal.cong(Bool, Bool,
          value => right || value,
          tail_left, tail_right, tail))

def guarded_and_cong(+guard: Bool,
  +left: Bool, +right: Bool,
  head: Laws.Truth(guard) ->
    {left == right : Bool}) ->
  {guard && left == guard && right : Bool}:
  match guard:
    case False{}:
      {==}
    case True{}:
      head(Unit{})

def drop_true_middle(+prefix: Bool,
  +before: Bool, +body: Bool,
  proof: Laws.Truth(before)) ->
  {prefix && (before && body) ==
    prefix && body : Bool}:
  match before:
    case True{}:
      {==}
    case False{}:
      match proof:

def truth_equals_true(+value: Bool,
  proof: Laws.Truth(value)) ->
  {value == True{} : Bool}:
  match value:
    case True{}:
      {==}
    case False{}:
      match proof:

def false_from_not_truth(+value: Bool,
  proof: Laws.Truth(Bool.not(value))) ->
  {value == False{} : Bool}:
  match value:
    case False{}:
      {==}
    case True{}:
      match proof:

def true_and_not_absurd(+value: Bool,
  yes: Laws.Truth(value),
  no: Laws.Truth(Bool.not(value))) -> Empty:
  match value:
    case True{}:
      match no:
    case False{}:
      match yes:

def black_all_head_cong(
  +scan: Retro.BlackReplyScan,
  +rank: U32, +capture: Bool,
  +legal: Bool, +child: Bool,
  safe: Laws.Truth(legal) ->
    Laws.Truth(Bool.not(capture)) ->
    {U32.is_ne(rank, 0) == child : Bool}) ->
  {Laws.BlackScanAll(
    Retro.black_reply_consider(scan,
      rank, capture, legal)) ==
    Laws.BlackScanAll(scan) &&
      (Bool.not(legal) ||
        (Bool.not(capture) && child)) : Bool}:
  match scan capture legal:
    case Retro.BlackReplyScan{seen,
         False{}, maximum} _ False{}:
      {==}
    case Retro.BlackReplyScan{seen,
         False{}, maximum} _ True{}:
      {==}
    case Retro.BlackReplyScan{seen,
         True{}, maximum} _ False{}:
      {==}
    case Retro.BlackReplyScan{seen,
         True{}, maximum} True{} True{}:
      {==}
    case Retro.BlackReplyScan{seen,
         True{}, maximum} False{} True{}:
      safe(Unit{}, Unit{})

def white_or_cong_without_pawn(
  +flag: Bool,
  +king_left: Bool, +king_right: Bool,
  +piece_left: Bool, +piece_right: Bool,
  +promotion_left: Bool,
  +promotion_right: Bool,
  no_pawn: Laws.Truth(Bool.not(flag)),
  king: {king_left == king_right : Bool},
  piece: {piece_left == piece_right : Bool}) ->
  {(king_left || piece_left) ||
      (flag && promotion_left) ==
    (king_right || piece_right) ||
      (flag && promotion_right) : Bool}:
  match flag:
    case True{}:
      match no_pawn:
    case False{}:
      Equal.trans(Bool,
        (king_left || piece_left) ||
          False{},
        (king_right || piece_left) ||
          False{},
        (king_right || piece_right) ||
          False{},
        Equal.cong(Bool, Bool,
          value => (value || piece_left) ||
            False{},
          king_left, king_right, king),
        Equal.cong(Bool, Bool,
          value => (king_right || value) ||
            False{},
          piece_left, piece_right, piece))

def bool_absorb_under_and(+a: Bool,
  +b: Bool, +c: Bool) ->
  {a || (b && (a || c)) ==
    a || (b && c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def black_body_cong(
  +before: Bool, +attack: Bool,
  +retro_has: Bool, +seen: Bool,
  +all: Bool, +has: Bool,
  +spec_all: Bool,
  has_eq: {retro_has == has : Bool},
  seen_eq: {seen == has : Bool},
  all_eq: {all == spec_all : Bool}) ->
  {(Bool.not(retro_has) && attack) ||
      (before &&
        ((Bool.not(seen) && attack) ||
          (seen && all))) ==
    (Bool.not(has) && attack) ||
      ((before && has) && spec_all) : Bool}:
  +mate = Bool.not(has) && attack
  +start = (Bool.not(retro_has) &&
    attack) || (before &&
      ((Bool.not(seen) && attack) ||
        (seen && all)))
  +one = mate || (before &&
    ((Bool.not(seen) && attack) ||
      (seen && all)))
  +two = mate || (before &&
    ((Bool.not(has) && attack) ||
      (has && all)))
  +three = mate || (before &&
    (mate || (has && spec_all)))
  +four = mate || (before &&
    (has && spec_all))
  +finish = mate ||
    ((before && has) && spec_all)
  Equal.trans(Bool, start, one, finish,
    Equal.cong(Bool, Bool,
      current =>
        (Bool.not(current) && attack) ||
          (before &&
            ((Bool.not(seen) && attack) ||
              (seen && all))),
      retro_has, has, has_eq),
    Equal.trans(Bool, one, two, finish,
      Equal.cong(Bool, Bool,
        current => mate || (before &&
          ((Bool.not(current) && attack) ||
            (current && all))),
        seen, has, seen_eq),
      Equal.trans(Bool, two, three,
        finish,
        Equal.cong(Bool, Bool,
          current => mate ||
            (before &&
              (mate || (has && current))),
          all, spec_all, all_eq),
        Equal.trans(Bool, three, four,
          finish,
          bool_absorb_under_and(mate,
            before, has && spec_all),
          Equal.cong(Bool, Bool,
            current => mate || current,
            before && (has && spec_all),
            (before && has) && spec_all,
            bool_and_assoc(before,
              has, spec_all))))))

def bool_and_false_right(+value: Bool) ->
  {value && False{} == False{} : Bool}:
  match value:
    case True{}:
      {==}
    case False{}:
      {==}

def bool_or_false_right(+value: Bool) ->
  {value || False{} == value : Bool}:
  match value:
    case True{}:
      {==}
    case False{}:
      {==}

def equality_cast(-A: Type, -P: A -> Type, -a: A, -b: A,
  equality: {a == b : A}, value: P(a)) -> P(b):
  %equality : P(_)
  value

def flip_bool_cmp(a: Bool, b: Bool) ->
  {Encoding.flip_cmp(Bool.cmp(a, b)) ==
    Bool.cmp(b, a) : Cmp}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def flip_cmp_fin(a: Bool, b: Bool, c: Cmp) ->
  {Encoding.flip_cmp(Word.cmp.fin(a, b, c)) ==
    Word.cmp.fin(b, a, Encoding.flip_cmp(c)) : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      flip_bool_cmp(a, b)
    case GT{}:
      {==}

def Laws.word_cmp_swap(n, a, b):
  match n:
    case 0n:
      {==}
    case 1n++rest:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          +cmp = Word.cmp(rest, at, bt)
          Equal.trans(Cmp,
            Encoding.flip_cmp(Word.cmp.fin(ab, bb,
              cmp)),
            Word.cmp.fin(bb, ab,
              Encoding.flip_cmp(cmp)),
            Word.cmp.fin(bb, ab,
              Word.cmp(rest, bt, at)),
            flip_cmp_fin(ab, bb, cmp),
            Equal.cong(Cmp, Cmp,
              value => Word.cmp.fin(bb, ab, value),
              Encoding.flip_cmp(cmp),
              Word.cmp(rest, bt, at),
              Laws.word_cmp_swap(rest, at, bt)))

def word_cmp_fin_self(bit: Bool) ->
  {Word.cmp.fin(bit, bit, EQ{}) == EQ{} : Cmp}:
  match bit:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.word_cmp_self_eq(n, a):
  match n:
    case 0n:
      {==}
    case 1n++rest:
      match a:
        case WCon{bit, tail}:
          Equal.trans(Cmp,
            Word.cmp.fin(bit, bit,
              Word.cmp(rest, tail, tail)),
            Word.cmp.fin(bit, bit, EQ{}),
            EQ{},
            Equal.cong(Cmp, Cmp,
              value => Word.cmp.fin(bit, bit, value),
              Word.cmp(rest, tail, tail), EQ{},
              Laws.word_cmp_self_eq(rest, tail)),
            word_cmp_fin_self(bit))

def Laws.u32_cmp_swap(a, b):
  match a b:
    case U32{aw} U32{bw}:
      Laws.word_cmp_swap(32n, aw, bw)

def Laws.u32_le_reflexive(a):
  match a:
    case U32{word}:
      equality_cast(Cmp,
        c => Laws.Truth(Cmp.is_le(c)),
        EQ{}, Word.cmp(32n, word, word),
        Equal.sym(Cmp, Word.cmp(32n, word,
          word), EQ{},
          Laws.word_cmp_self_eq(32n, word)),
        Unit{})

def cmp_lt_implies_le(c: Cmp,
  less: Laws.Truth(Cmp.is_lt(c))) ->
  Laws.Truth(Cmp.is_le(c)):
  match c:
    case LT{}:
      Unit{}
    case EQ{}:
      Empty.absurd(Laws.Truth(True{}), less)
    case GT{}:
      Empty.absurd(Laws.Truth(False{}), less)

def u32_reverse_le_from_cmp(+a: U32, +b: U32,
  +cmp: Cmp, equality: {U32.cmp(a, b) == cmp : Cmp},
  reverse: Laws.Truth(Cmp.is_le(
    Encoding.flip_cmp(cmp)))) ->
  Laws.Truth(U32.is_le(b, a)):
  actual = Equal.trans(Cmp,
    Encoding.flip_cmp(cmp),
    Encoding.flip_cmp(U32.cmp(a, b)),
    U32.cmp(b, a),
    Equal.cong(Cmp, Cmp, Encoding.flip_cmp,
      cmp, U32.cmp(a, b),
      Equal.sym(Cmp, U32.cmp(a, b), cmp,
        equality)),
    Laws.u32_cmp_swap(a, b))
  equality_cast(Cmp,
    c => Laws.Truth(Cmp.is_le(c)),
    Encoding.flip_cmp(cmp), U32.cmp(b, a),
    actual, reverse)

def u32_max_upper_left_by_cmp(+a: U32, +b: U32,
  cmp: Cmp,
  +equality: {U32.cmp(a, b) == cmp : Cmp}) ->
  Laws.Truth(U32.is_le(a, U32.max(a, b))):
  match cmp:
    case LT{}:
      actual_lt = equality_cast(Cmp,
        c => Laws.Truth(Cmp.is_lt(c)),
        LT{}, U32.cmp(a, b),
        Equal.sym(Cmp, U32.cmp(a, b), LT{},
          equality), Unit{})
      branch = cmp_lt_implies_le(
        U32.cmp(a, b), actual_lt)
      equality_cast(Cmp,
        c => Laws.Truth(U32.is_le(a,
          Bool.pick(U32, Cmp.is_lt(c), b, a))),
        LT{}, U32.cmp(a, b),
        Equal.sym(Cmp, U32.cmp(a, b), LT{},
          equality), branch)
    case EQ{}:
      equality_cast(Cmp,
        c => Laws.Truth(U32.is_le(a,
          Bool.pick(U32, Cmp.is_lt(c), b, a))),
        EQ{}, U32.cmp(a, b),
        Equal.sym(Cmp, U32.cmp(a, b), EQ{},
          equality), Laws.u32_le_reflexive(a))
    case GT{}:
      equality_cast(Cmp,
        c => Laws.Truth(U32.is_le(a,
          Bool.pick(U32, Cmp.is_lt(c), b, a))),
        GT{}, U32.cmp(a, b),
        Equal.sym(Cmp, U32.cmp(a, b), GT{},
          equality), Laws.u32_le_reflexive(a))

def Laws.u32_max_upper_left(a, b):
  u32_max_upper_left_by_cmp(a, b,
    U32.cmp(a, b), {==})

def u32_max_upper_right_by_cmp(+a: U32, +b: U32,
  cmp: Cmp,
  +equality: {U32.cmp(a, b) == cmp : Cmp}) ->
  Laws.Truth(U32.is_le(b, U32.max(a, b))):
  match cmp:
    case LT{}:
      equality_cast(Cmp,
        c => Laws.Truth(U32.is_le(b,
          Bool.pick(U32, Cmp.is_lt(c), b, a))),
        LT{}, U32.cmp(a, b),
        Equal.sym(Cmp, U32.cmp(a, b), LT{},
          equality), Laws.u32_le_reflexive(b))
    case EQ{}:
      branch = u32_reverse_le_from_cmp(a, b,
        EQ{}, equality, Unit{})
      equality_cast(Cmp,
        c => Laws.Truth(U32.is_le(b,
          Bool.pick(U32, Cmp.is_lt(c), b, a))),
        EQ{}, U32.cmp(a, b),
        Equal.sym(Cmp, U32.cmp(a, b), EQ{},
          equality), branch)
    case GT{}:
      branch = u32_reverse_le_from_cmp(a, b,
        GT{}, equality, Unit{})
      equality_cast(Cmp,
        c => Laws.Truth(U32.is_le(b,
          Bool.pick(U32, Cmp.is_lt(c), b, a))),
        GT{}, U32.cmp(a, b),
        Equal.sym(Cmp, U32.cmp(a, b), GT{},
          equality), branch)

def Laws.u32_max_upper_right(a, b):
  u32_max_upper_right_by_cmp(a, b,
    U32.cmp(a, b), {==})

def u32_max_bound_by_cmp(+a: U32, +b: U32,
  +limit: U32, cmp: Cmp,
  a_bounded: Laws.Truth(U32.is_le(a, limit)),
  b_bounded: Laws.Truth(U32.is_le(b, limit))) ->
  Laws.Truth(U32.is_le(
    Bool.pick(U32, Cmp.is_lt(cmp), b, a),
    limit)):
  match cmp:
    case LT{}:
      b_bounded
    case EQ{}:
      a_bounded
    case GT{}:
      a_bounded

def Laws.u32_max_preserves_upper_bound(a, b,
  limit, a_bounded, b_bounded):
  u32_max_bound_by_cmp(a, b, limit,
    U32.cmp(a, b), a_bounded, b_bounded)

def bool_cmp_chain(a: Bool, b: Bool, c: Bool) ->
  Laws.Truth(Laws.CmpChain(Bool.cmp(a, b),
    Bool.cmp(b, c), Bool.cmp(a, c))):
  match a b c:
    case False{} False{} False{}:
      Unit{}
    case False{} False{} True{}:
      Unit{}
    case False{} True{} False{}:
      Unit{}
    case False{} True{} True{}:
      Unit{}
    case True{} False{} False{}:
      Unit{}
    case True{} False{} True{}:
      Unit{}
    case True{} True{} False{}:
      Unit{}
    case True{} True{} True{}:
      Unit{}

def chain_lt_any_lt(c: Cmp) ->
  Laws.Truth(Laws.CmpChain(LT{}, c, LT{})):
  match c:
    case LT{}:
      Unit{}
    case EQ{}:
      Unit{}
    case GT{}:
      Unit{}

def chain_any_lt_lt(c: Cmp) ->
  Laws.Truth(Laws.CmpChain(c, LT{}, LT{})):
  match c:
    case LT{}:
      Unit{}
    case EQ{}:
      Unit{}
    case GT{}:
      Unit{}

def chain_any_gt_gt(c: Cmp) ->
  Laws.Truth(Laws.CmpChain(c, GT{}, GT{})):
  match c:
    case LT{}:
      Unit{}
    case EQ{}:
      Unit{}
    case GT{}:
      Unit{}

def chain_gt_any_gt(c: Cmp) ->
  Laws.Truth(Laws.CmpChain(GT{}, c, GT{})):
  match c:
    case LT{}:
      Unit{}
    case EQ{}:
      Unit{}
    case GT{}:
      Unit{}

def cmp_fin_chain(+a: Bool, +b: Bool, +c: Bool,
  ab: Cmp, bc: Cmp, ac: Cmp,
  chain: Laws.Truth(Laws.CmpChain(ab, bc, ac))) ->
  Laws.Truth(Laws.CmpChain(
    Word.cmp.fin(a, b, ab),
    Word.cmp.fin(b, c, bc),
    Word.cmp.fin(a, c, ac))):
  match ab bc:
    case LT{} LT{}:
      match ac:
        case LT{}:
          Unit{}
        case EQ{}:
          match chain:
        case GT{}:
          match chain:
    case LT{} EQ{}:
      match ac:
        case LT{}:
          chain_lt_any_lt(Bool.cmp(b, c))
        case EQ{}:
          match chain:
        case GT{}:
          match chain:
    case LT{} GT{}:
      Unit{}
    case EQ{} LT{}:
      match ac:
        case LT{}:
          chain_any_lt_lt(Bool.cmp(a, b))
        case EQ{}:
          match chain:
        case GT{}:
          match chain:
    case EQ{} EQ{}:
      match ac:
        case LT{}:
          match chain:
        case EQ{}:
          bool_cmp_chain(a, b, c)
        case GT{}:
          match chain:
    case EQ{} GT{}:
      match ac:
        case LT{}:
          match chain:
        case EQ{}:
          match chain:
        case GT{}:
          chain_any_gt_gt(Bool.cmp(a, b))
    case GT{} LT{}:
      Unit{}
    case GT{} EQ{}:
      match ac:
        case LT{}:
          match chain:
        case EQ{}:
          match chain:
        case GT{}:
          chain_gt_any_gt(Bool.cmp(b, c))
    case GT{} GT{}:
      match ac:
        case LT{}:
          match chain:
        case EQ{}:
          match chain:
        case GT{}:
          Unit{}

def Laws.word_cmp_chain(n, a, b, c):
  match n:
    case 0n:
      Unit{}
    case 1n++rest:
      match a b c:
        case WCon{ab, at} WCon{bc, bt} WCon{cc, ct}:
          cmp_fin_chain(ab, bc, cc,
            Word.cmp(rest, at, bt),
            Word.cmp(rest, bt, ct),
            Word.cmp(rest, at, ct),
            Laws.word_cmp_chain(rest, at, bt, ct))

def cmp_chain_le_trans(ab: Cmp, bc: Cmp,
  ac: Cmp,
  ab_le: Laws.Truth(Cmp.is_le(ab)),
  bc_le: Laws.Truth(Cmp.is_le(bc)),
  chain: Laws.Truth(Laws.CmpChain(ab, bc, ac))) ->
  Laws.Truth(Cmp.is_le(ac)):
  match ab bc:
    case LT{} LT{}:
      match ac:
        case LT{}:
          Unit{}
        case EQ{}:
          Unit{}
        case GT{}:
          Empty.absurd(Laws.Truth(False{}), chain)
    case LT{} EQ{}:
      match ac:
        case LT{}:
          Unit{}
        case EQ{}:
          Unit{}
        case GT{}:
          Empty.absurd(Laws.Truth(False{}), chain)
    case LT{} GT{}:
      Empty.absurd(Laws.Truth(Cmp.is_le(ac)), bc_le)
    case EQ{} LT{}:
      match ac:
        case LT{}:
          Unit{}
        case EQ{}:
          Unit{}
        case GT{}:
          Empty.absurd(Laws.Truth(False{}), chain)
    case EQ{} EQ{}:
      match ac:
        case LT{}:
          Unit{}
        case EQ{}:
          Unit{}
        case GT{}:
          Empty.absurd(Laws.Truth(False{}), chain)
    case EQ{} GT{}:
      Empty.absurd(Laws.Truth(Cmp.is_le(ac)), bc_le)
    case GT{} LT{}:
      Empty.absurd(Laws.Truth(Cmp.is_le(ac)), ab_le)
    case GT{} EQ{}:
      Empty.absurd(Laws.Truth(Cmp.is_le(ac)), ab_le)
    case GT{} GT{}:
      Empty.absurd(Laws.Truth(Cmp.is_le(ac)), ab_le)

def Laws.u32_le_transitive(a, b, c, ab, bc):
  match a b c:
    case U32{aw} U32{bw} U32{cw}:
      cmp_chain_le_trans(
        Word.cmp(32n, aw, bw),
        Word.cmp(32n, bw, cw),
        Word.cmp(32n, aw, cw),
        ab, bc,
        Laws.word_cmp_chain(32n, aw, bw, cw))

def cmp_fin_true_true(c: Cmp) ->
  {Word.cmp.fin(True{}, True{}, c) == c : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def cmp_fin_true_false_tail_lt(c: Cmp,
  less: Laws.Truth(Cmp.is_lt(c))) ->
  Laws.Truth(Cmp.is_lt(
    Word.cmp.fin(True{}, False{}, c))):
  match c:
    case LT{}:
      Unit{}
    case EQ{}:
      match less:
    case GT{}:
      match less:

def Laws.word_inc_strict_below_ones(n, word,
  less):
  match n:
    case 0n:
      match less:
    case 1n++rest:
      match word:
        case WCon{False{}, tail}:
          equality_cast(Cmp,
            c => Laws.Truth(Cmp.is_lt(
              Word.cmp.fin(False{}, True{}, c))),
            EQ{}, Word.cmp(rest, tail, tail),
            Equal.sym(Cmp,
              Word.cmp(rest, tail, tail), EQ{},
              Laws.word_cmp_self_eq(rest, tail)),
            Unit{})
        case WCon{True{}, tail}:
          +tail_cmp = Word.cmp(rest, tail,
            Encoding.ones(rest))
          tail_less = equality_cast(Cmp,
            c => Laws.Truth(Cmp.is_lt(c)),
            Word.cmp.fin(True{}, True{}, tail_cmp),
            tail_cmp,
            cmp_fin_true_true(tail_cmp), less)
          cmp_fin_true_false_tail_lt(
            Word.cmp(rest, tail,
              Word.inc(rest, tail)),
            Laws.word_inc_strict_below_ones(rest,
              tail, tail_less))

def Laws.u32_all_ones_is_max():
  {==}

def Laws.u32_inc_strict_below_max(x, less):
  match x:
    case U32{word}:
      Laws.word_inc_strict_below_ones(32n,
        word, less)

def cmp_chain_le_lt(ab: Cmp, bc: Cmp,
  ac: Cmp,
  ab_le: Laws.Truth(Cmp.is_le(ab)),
  bc_lt: Laws.Truth(Cmp.is_lt(bc)),
  chain: Laws.Truth(Laws.CmpChain(ab, bc, ac))) ->
  Laws.Truth(Cmp.is_lt(ac)):
  match ab bc:
    case LT{} LT{}:
      match ac:
        case LT{}:
          Unit{}
        case EQ{}:
          match chain:
        case GT{}:
          match chain:
    case EQ{} LT{}:
      match ac:
        case LT{}:
          Unit{}
        case EQ{}:
          match chain:
        case GT{}:
          match chain:
    case GT{} LT{}:
      match ab_le:
    case LT{} EQ{}:
      match bc_lt:
    case LT{} GT{}:
      match bc_lt:
    case EQ{} EQ{}:
      match bc_lt:
    case EQ{} GT{}:
      match bc_lt:
    case GT{} EQ{}:
      match ab_le:
    case GT{} GT{}:
      match ab_le:

def Laws.u32_le_lt_transitive(a, b, c, ab, bc):
  match a b c:
    case U32{aw} U32{bw} U32{cw}:
      cmp_chain_le_lt(
        Word.cmp(32n, aw, bw),
        Word.cmp(32n, bw, cw),
        Word.cmp(32n, aw, cw),
        ab, bc,
        Laws.word_cmp_chain(32n, aw, bw, cw))

def square_member_append_left(-A: Data, +x: A,
  xs: List<&2, A>, +ys: List<&2, A>,
  found: Squares.Member(A, x, xs)) ->
  Squares.Member(A, x, List.append(&2, A, xs, ys)):
  match xs:
    case Nil{}:
      match found:
    case head <> tail:
      match found:
        case Inl{equal}:
          Inl{equal}
        case Inr{later}:
          Inr{square_member_append_left(A, x,
            tail, ys, later)}

def square_member_append_right(-A: Data, +x: A,
  xs: List<&2, A>, +ys: List<&2, A>,
  found: Squares.Member(A, x, ys)) ->
  Squares.Member(A, x, List.append(&2, A, xs, ys)):
  match xs:
    case Nil{}:
      found
    case head <> tail:
      Inr{square_member_append_right(A, x,
        tail, ys, found)}

def square_member_prefix(n: Nat, +bit: Bool,
  +x: Word(n), xs: List<&2, Word(n)>,
  found: Squares.Member(Word(n), x, xs)) ->
  Squares.Member(Word(1n+n), WCon{bit, x},
    Squares.prefix(n, bit, xs)):
  match xs:
    case Nil{}:
      match found:
    case head <> tail:
      match found:
        case Inl{equal}:
          Inl{Equal.cong(Word(n), Word(1n+n),
            word => WCon{bit, word}, x, head, equal)}
        case Inr{later}:
          Inr{square_member_prefix(n, bit,
            x, tail, later)}

def Laws.square_words_complete(n, word):
  match n:
    case 0n:
      match word:
        case WNil{}:
          Inl{{==}}
    case 1n++rest:
      match word:
        case WCon{bit, tail}:
          match bit:
            case False{}:
              found = Laws.square_words_complete(rest, tail)
              square_member_append_left(
                Word(1n+rest), WCon{False{}, tail},
                Squares.prefix(rest, False{}, Squares.words(rest)),
                Squares.prefix(rest, True{}, Squares.words(rest)),
                square_member_prefix(rest, False{},
                  tail, Squares.words(rest), found))
            case True{}:
              found = Laws.square_words_complete(rest, tail)
              square_member_append_right(
                Word(1n+rest), WCon{True{}, tail},
                Squares.prefix(rest, False{}, Squares.words(rest)),
                Squares.prefix(rest, True{}, Squares.words(rest)),
                square_member_prefix(rest, True{},
                  tail, Squares.words(rest), found))

def square_member_encode(+word: Word(6n),
  xs: List<&2, Word(6n)>,
  found: Squares.Member(Word(6n), word, xs)) ->
  Squares.Member(U32, Encoding.square(word),
    Squares.encode(xs)):
  match xs:
    case Nil{}:
      match found:
    case head <> tail:
      match found:
        case Inl{equal}:
          Inl{Equal.cong(Word(6n), U32,
            Encoding.square, word, head, equal)}
        case Inr{later}:
          Inr{square_member_encode(word, tail, later)}

def cmp_fin_zero_not_lt(+bit: Bool, +tail: Cmp,
  prior: Laws.NotLT(tail)) ->
  Laws.NotLT(Word.cmp.fin(bit, False{}, tail)):
  match bit tail:
    case False{} LT{}:
      Empty.absurd(Laws.NotLT(
        Word.cmp.fin(False{}, False{}, LT{})), prior)
    case True{} LT{}:
      Empty.absurd(Laws.NotLT(
        Word.cmp.fin(True{}, False{}, LT{})), prior)
    case False{} EQ{}:
      Unit{}
    case True{} EQ{}:
      Unit{}
    case False{} GT{}:
      Unit{}
    case True{} GT{}:
      Unit{}

def Laws.word_cmp_zero_not_lt(n, word):
  match n:
    case 0n:
      match word:
        case WNil{}:
          Unit{}
    case 1n++p:
      match word:
        case WCon{bit, tail}:
          cmp_fin_zero_not_lt(bit,
            Word.cmp(p, tail, Word.zero(p)),
            Laws.word_cmp_zero_not_lt(p, tail))

def cmp_fin_one_lt_requires_zero_tail(+bit: Bool, +tail: Cmp,
  not_lower: Laws.NotLT(tail),
  less: Laws.Truth(Cmp.is_lt(
    Word.cmp.fin(bit, True{}, tail)))) ->
  Laws.Truth(Cmp.is_eq(tail)) & Laws.Truth(Bool.not(bit)):
  match bit tail:
    case False{} LT{}:
      Empty.absurd(
        Laws.Truth(Cmp.is_eq(LT{})) &
          Laws.Truth(Bool.not(False{})), not_lower)
    case True{} LT{}:
      Empty.absurd(
        Laws.Truth(Cmp.is_eq(LT{})) &
          Laws.Truth(Bool.not(True{})), not_lower)
    case False{} EQ{}:
      (Unit{}, Unit{})
    case True{} EQ{}:
      Empty.absurd(
        Laws.Truth(Cmp.is_eq(EQ{})) &
          Laws.Truth(Bool.not(True{})), less)
    case False{} GT{}:
      Empty.absurd(
        Laws.Truth(Cmp.is_eq(GT{})) &
          Laws.Truth(Bool.not(False{})), less)
    case True{} GT{}:
      Empty.absurd(
        Laws.Truth(Cmp.is_eq(GT{})) &
          Laws.Truth(Bool.not(True{})), less)

def cmp_fin_zero_lt_implies_lt(+bit: Bool, +tail: Cmp,
  less: Laws.Truth(Cmp.is_lt(
    Word.cmp.fin(bit, False{}, tail)))) ->
  Laws.Truth(Cmp.is_lt(tail)):
  match bit tail:
    case False{} LT{}:
      Unit{}
    case True{} LT{}:
      Unit{}
    case False{} EQ{}:
      Empty.absurd(Laws.Truth(Cmp.is_lt(EQ{})), less)
    case True{} EQ{}:
      Empty.absurd(Laws.Truth(Cmp.is_lt(EQ{})), less)
    case False{} GT{}:
      Empty.absurd(Laws.Truth(Cmp.is_lt(GT{})), less)
    case True{} GT{}:
      Empty.absurd(Laws.Truth(Cmp.is_lt(GT{})), less)

def Laws.low_zero_prefix_lt_implies_high_lt(n, low,
  high_cmp, less):
  match n:
    case 0n:
      less
    case 1n++p:
      match low:
        case WCon{bit, tail}:
          Laws.low_zero_prefix_lt_implies_high_lt(
            p, tail, high_cmp,
            cmp_fin_zero_lt_implies_lt(bit,
              Encoding.cmp_low_zero(p, tail, high_cmp),
              less))

def Laws.word_cmp_append_zero_prefix(n, m, low,
  high, threshold):
  match n:
    case 0n:
      match low:
        case WNil{}:
          {==}
    case 1n++p:
      match low:
        case WCon{bit, rest}:
          Equal.cong(Cmp, Cmp,
            result => Word.cmp.fin(bit, False{}, result),
            Word.cmp(Nat.add(p, m),
              Encoding.append(m, p, rest, high),
              Encoding.append(m, p,
                Word.zero(p), threshold)),
            Encoding.cmp_low_zero(p, rest,
              Word.cmp(m, high, threshold)),
            Laws.word_cmp_append_zero_prefix(p, m,
              rest, high, threshold))

def Laws.structural_sixty_four_is_64():
  {==}

def Laws.structural_two_is_2():
  {==}

def Laws.low_one_bit_matches_split(word):
  match word:
    case WCon{bit, rest}:
      {==}

def Laws.uniform_array_size(d, value):
  match d:
    case 0n:
      {==}
    case 1n+p:
      %Laws.uniform_array_size(p, value) :
        {Array.size.node(U32,
          Array.new(U32, p, value),
          Array.size(U32, Array.new(U32, p, value))) ==
          Array.size.node(U32,
            Array.new(U32, p, value), _) :
          Array<U32> & U32}
      {==}

def Laws.word_split_append_inverse(n, m, low, high):
  match n:
    case 0n:
      match low:
        case WNil{}:
          {==}
    case 1n+p:
      match low:
        case WCon{bit, rest}:
          %Laws.word_split_append_inverse(p, m, rest, high) :
            {Encoding.split.prepend(p, m, bit,
              Encoding.split(m, p,
                Encoding.append(m, p, rest, high))) ==
              Encoding.split.prepend(p, m, bit, _) :
              Word(1n+p) & Word(m)}
          {==}

def Laws.word_and_ones(n, word):
  match n:
    case 0n:
      match word:
        case WNil{}:
          {==}
    case 1n+p:
      match word:
        case WCon{bit, tail}:
          match bit:
            case False{}:
              %Laws.word_and_ones(p, tail) :
                {WCon{False{}, Word.and(p, tail,
                  Encoding.ones(p))} == WCon{False{}, _} :
                  Word(1n+p)}
              {==}
            case True{}:
              %Laws.word_and_ones(p, tail) :
                {WCon{True{}, Word.and(p, tail,
                  Encoding.ones(p))} == WCon{True{}, _} :
                  Word(1n+p)}
              {==}

def Laws.word_and_zero(n, word):
  match n:
    case 0n:
      match word:
        case WNil{}:
          {==}
    case 1n+p:
      match word:
        case WCon{bit, tail}:
          match bit:
            case False{}:
              %Laws.word_and_zero(p, tail) :
                {WCon{False{}, Word.and(p, tail,
                  Word.zero(p))} == WCon{False{}, _} :
                  Word(1n+p)}
              {==}
            case True{}:
              %Laws.word_and_zero(p, tail) :
                {WCon{False{}, Word.and(p, tail,
                  Word.zero(p))} == WCon{False{}, _} :
                  Word(1n+p)}
              {==}

def Laws.word_or_zero(n, word):
  match n:
    case 0n:
      match word:
        case WNil{}:
          {==}
    case 1n+p:
      match word:
        case WCon{bit, tail}:
          match bit:
            case False{}:
              %Laws.word_or_zero(p, tail) :
                {WCon{False{}, Word.or(p, tail,
                  Word.zero(p))} == WCon{False{}, _} :
                  Word(1n+p)}
              {==}
            case True{}:
              %Laws.word_or_zero(p, tail) :
                {WCon{True{}, Word.or(p, tail,
                  Word.zero(p))} == WCon{True{}, _} :
                  Word(1n+p)}
              {==}

def Laws.word_zero_or(n, word):
  match n:
    case 0n:
      match word:
        case WNil{}:
          {==}
    case 1n+p:
      match word:
        case WCon{bit, tail}:
          match bit:
            case False{}:
              %Laws.word_zero_or(p, tail) :
                {WCon{False{}, Word.or(p,
                  Word.zero(p), tail)} == WCon{False{}, _} :
                  Word(1n+p)}
              {==}
            case True{}:
              %Laws.word_zero_or(p, tail) :
                {WCon{True{}, Word.or(p,
                  Word.zero(p), tail)} == WCon{True{}, _} :
                  Word(1n+p)}
              {==}

def Laws.word_or_append(n, m, a, b, c, d):
  match n:
    case 0n:
      match a c:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a c:
        case WCon{ah, at} WCon{ch, ct}:
          %Laws.word_or_append(p, m, at, b, ct, d) :
            {WCon{Bool.or(ah, ch),
              Word.or(Nat.add(p, m),
                Encoding.append(m, p, at, b),
                Encoding.append(m, p, ct, d))} ==
              WCon{Bool.or(ah, ch), _} :
              Word(1n+Nat.add(p, m))}
          {==}

def Laws.word_or_disjoint(n, m, low, high):
  +zero_low = Word.zero(n)
  +zero_high = Word.zero(m)
  distributed = Laws.word_or_append(n, m,
    low, zero_high, zero_low, high)
  low_clean = Equal.cong(Word(n), Word(Nat.add(n, m)),
    head => Encoding.append(m, n, head,
      Word.or(m, zero_high, high)),
    Word.or(n, low, zero_low), low,
    Laws.word_or_zero(n, low))
  high_clean = Equal.cong(Word(m), Word(Nat.add(n, m)),
    tail => Encoding.append(m, n, low, tail),
    Word.or(m, zero_high, high), high,
    Laws.word_zero_or(m, high))
  first = Equal.trans(Word(Nat.add(n, m)),
    Word.or(Nat.add(n, m),
      Encoding.append(m, n, low, zero_high),
      Encoding.append(m, n, zero_low, high)),
    Encoding.append(m, n,
      Word.or(n, low, zero_low),
      Word.or(m, zero_high, high)),
    Encoding.append(m, n, low,
      Word.or(m, zero_high, high)),
    distributed, low_clean)
  Equal.trans(Word(Nat.add(n, m)),
    Word.or(Nat.add(n, m),
      Encoding.append(m, n, low, zero_high),
      Encoding.append(m, n, zero_low, high)),
    Encoding.append(m, n, low,
      Word.or(m, zero_high, high)),
    Encoding.append(m, n, low, high),
    first, high_clean)

def Laws.word_or_into_tail(n, m, low, tail, incoming):
  +zero_low = Word.zero(n)
  distributed = Laws.word_or_append(n, m,
    low, tail, zero_low, incoming)
  cleaned = Equal.cong(Word(n), Word(Nat.add(n, m)),
    head => Encoding.append(m, n, head,
      Word.or(m, tail, incoming)),
    Word.or(n, low, zero_low), low,
    Laws.word_or_zero(n, low))
  Equal.trans(Word(Nat.add(n, m)),
    Word.or(Nat.add(n, m),
      Encoding.append(m, n, low, tail),
      Encoding.append(m, n, zero_low, incoming)),
    Encoding.append(m, n,
      Word.or(n, low, zero_low),
      Word.or(m, tail, incoming)),
    Encoding.append(m, n, low,
      Word.or(m, tail, incoming)),
    distributed, cleaned)

def Laws.word_shr_pad_commutes(n, word):
  match n:
    case 0n:
      match word:
        case WNil{}:
          {==}
    case 1n+p:
      match word:
        case WCon{bit, tail}:
          {==}

def Laws.word_shrn_outer_commutes(size, count, word):
  match count:
    case 0n:
      {==}
    case 1n+rest:
      Laws.word_shrn_outer_commutes(size, rest,
        Word.shr(size, word))

def Laws.word_shrn_inner_equals_outer(size, count, word):
  match count:
    case 0n:
      {==}
    case 1n++rest:
      lifted = Equal.cong(Word(size), Word(size),
        value => Word.shr(size, value),
        Encoding.shrn.inner(size, rest, word),
        Encoding.shrn.outer(size, rest, word),
        Laws.word_shrn_inner_equals_outer(size, rest, word))
      Equal.trans(Word(size),
        Word.shr(size,
          Encoding.shrn.inner(size, rest, word)),
        Word.shr(size,
          Encoding.shrn.outer(size, rest, word)),
        Encoding.shrn.outer(size, rest,
          Word.shr(size, word)),
        lifted,
        Equal.sym(Word(size),
          Encoding.shrn.outer(size, rest,
            Word.shr(size, word)),
          Word.shr(size,
            Encoding.shrn.outer(size, rest, word)),
          Laws.word_shrn_outer_commutes(size, rest, word)))

def Laws.word_shrn_outer_pad_commutes(size, count, word):
  match count:
    case 0n:
      {==}
    case 1n++rest:
      first = Equal.cong(Word(1n+size), Word(1n+size),
        value => Encoding.shrn.outer(1n+size, rest, value),
        Word.shr(1n+size, Word.shr.pad(size, word)),
        Word.shr.pad(size, Word.shr(size, word)),
        Laws.word_shr_pad_commutes(size, word))
      second = Laws.word_shrn_outer_pad_commutes(size,
        rest, Word.shr(size, word))
      Equal.trans(Word(1n+size),
        Encoding.shrn.outer(1n+size, rest,
          Word.shr(1n+size, Word.shr.pad(size, word))),
        Encoding.shrn.outer(1n+size, rest,
          Word.shr.pad(size, Word.shr(size, word))),
        Word.shr.pad(size,
          Encoding.shrn.outer(size, rest,
            Word.shr(size, word))),
        first, second)

def Laws.word_shrn_append_drop(n, m, low, high):
  match n:
    case 0n:
      match low:
        case WNil{}:
          {==}
    case 1n++p:
      match low:
        case WCon{bit, rest}:
          +tail = Encoding.append(m, p, rest, high)
          +size = Nat.add(p, m)
          commute = Laws.word_shrn_outer_pad_commutes(
            size, p, tail)
          child = Laws.word_shrn_append_drop(p, m, rest, high)
          lifted = Equal.cong(Word(size), Word(1n+size),
            value => Word.shr.pad(size, value),
            Encoding.shrn.outer(size, p, tail),
            Encoding.padn(m, p, high), child)
          Equal.trans(Word(1n+size),
            Encoding.shrn.outer(1n+size, p,
              Word.shr.pad(size, tail)),
            Word.shr.pad(size,
              Encoding.shrn.outer(size, p, tail)),
            Word.shr.pad(size,
              Encoding.padn(m, p, high)),
            commute, lifted)

def Laws.word_shrn_inner_append_drop(n, m, low, high):
  +packed = Encoding.append(m, n, low, high)
  Equal.trans(Word(Nat.add(n, m)),
    Encoding.shrn.inner(Nat.add(n, m), n, packed),
    Encoding.shrn.outer(Nat.add(n, m), n, packed),
    Encoding.padn(m, n, high),
    Laws.word_shrn_inner_equals_outer(Nat.add(n, m), n, packed),
    Laws.word_shrn_append_drop(n, m, low, high))

def Laws.six_bit_prefix_survives_six_zero_pads(rest):
  match rest:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, tail}}}}}}:
      {==}

def Laws.low_six_bits_of_packed_word(low, high):
  match low:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WNil{}}}}}}}:
      {==}

def Laws.second_six_bits_of_nested_word(bits, tail):
  match bits:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WNil{}}}}}}}:
      {==}

def Laws.third_six_bits_of_nested_word(bits, tail):
  match bits:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WNil{}}}}}}}:
      {==}

def Laws.six_bit_prefix_survives_twelve_zero_pads(rest):
  match rest:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, tail}}}}}}:
      {==}

def Laws.eighteen_pads_make_clean_turn(bit):
  match bit:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.eighteen_pads_make_turn(bits):
  match bits:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WCon{b6, WCon{b7,
      WCon{b8, WCon{b9, WCon{b10, WCon{b11,
      WCon{b12, WCon{b13, WNil{}}}}}}}}}}}}}}}:
      {==}

def Laws.regroup_first_two_squares(wk, bk, high):
  match wk bk:
    case WCon{a0, WCon{a1, WCon{a2, WCon{a3,
      WCon{a4, WCon{a5, WNil{}}}}}}}
      WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WNil{}}}}}}}:
      {==}

def Laws.regroup_first_three_squares(wk, bk, pc, high):
  match wk bk pc:
    case WCon{a0, WCon{a1, WCon{a2, WCon{a3,
      WCon{a4, WCon{a5, WNil{}}}}}}}
      WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WNil{}}}}}}}
      WCon{c0, WCon{c1, WCon{c2, WCon{c3,
      WCon{c4, WCon{c5, WNil{}}}}}}}:
      {==}

def Laws.u32_shrn_is_word_inner(count, word):
  match count:
    case 0n:
      {==}
    case 1n+rest:
      Equal.cong(U32, U32,
        value => U32.shr(value),
        U32.shrn(U32{word}, rest),
        U32{Encoding.shrn.inner(32n, rest, word)},
        Laws.u32_shrn_is_word_inner(rest, word))

def Laws.u32_shrn_drops_six_low_bits(low, high):
  +packed = Encoding.append(26n, 6n, low, high)
  first = Laws.u32_shrn_is_word_inner(6n, packed)
  second = Equal.cong(Word(32n), U32,
    value => U32{value},
    Encoding.shrn.inner(32n, 6n, packed),
    Encoding.shrn.outer(32n, 6n, packed),
    Laws.word_shrn_inner_equals_outer(32n, 6n, packed))
  third = Equal.cong(Word(32n), U32,
    value => U32{value},
    Encoding.shrn.outer(32n, 6n, packed),
    Encoding.padn(26n, 6n, high),
    Laws.word_shrn_append_drop(6n, 26n, low, high))
  part = Equal.trans(U32,
    U32.shrn(U32{packed}, 6n),
    U32{Encoding.shrn.inner(32n, 6n, packed)},
    U32{Encoding.shrn.outer(32n, 6n, packed)},
    first, second)
  Equal.trans(U32,
    U32.shrn(U32{packed}, 6n),
    U32{Encoding.shrn.outer(32n, 6n, packed)},
    U32{Encoding.padn(26n, 6n, high)},
    part, third)

def Laws.u32_shrn_drops_twelve_low_bits(low, high):
  +packed = Encoding.append(20n, 12n, low, high)
  first = Laws.u32_shrn_is_word_inner(12n, packed)
  second = Equal.cong(Word(32n), U32,
    value => U32{value},
    Encoding.shrn.inner(32n, 12n, packed),
    Encoding.padn(20n, 12n, high),
    Laws.word_shrn_inner_append_drop(12n, 20n, low, high))
  Equal.trans(U32,
    U32.shrn(U32{packed}, 12n),
    U32{Encoding.shrn.inner(32n, 12n, packed)},
    U32{Encoding.padn(20n, 12n, high)},
    first, second)

def Laws.u32_shrn_drops_eighteen_low_bits(low, high):
  +packed = Encoding.append(14n, 18n, low, high)
  first = Laws.u32_shrn_is_word_inner(18n, packed)
  second = Equal.cong(Word(32n), U32,
    value => U32{value},
    Encoding.shrn.inner(32n, 18n, packed),
    Encoding.padn(14n, 18n, high),
    Laws.word_shrn_inner_append_drop(18n, 14n, low, high))
  Equal.trans(U32,
    U32.shrn(U32{packed}, 18n),
    U32{Encoding.shrn.inner(32n, 18n, packed)},
    U32{Encoding.padn(14n, 18n, high)},
    first, second)

def Laws.word_and_append(n, m, a, b, c, d):
  match n:
    case 0n:
      match a c:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a c:
        case WCon{ah, at} WCon{ch, ct}:
          %Laws.word_and_append(p, m, at, b, ct, d) :
            {WCon{Bool.and(ah, ch),
              Word.and(Nat.add(p, m),
                Encoding.append(m, p, at, b),
                Encoding.append(m, p, ct, d))} ==
              WCon{Bool.and(ah, ch), _} :
              Word(1n+Nat.add(p, m))}
          {==}

def Laws.structural_six_bit_mask_is_63():
  {==}

def Laws.shift_six_square(bits):
  match bits:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WNil{}}}}}}}:
      {==}

def Laws.shift_twelve_square(bits):
  match bits:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WNil{}}}}}}}:
      {==}

def Laws.mask_clean_turn(bit):
  match bit:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.fast_turn_mask_matches_structural_bit(turn):
  match turn:
    case U32{word}:
      match word:
        case WCon{bit, tail}:
          match bit:
            case True{}:
              Equal.cong(Word(31n), U32,
                rest => U32{WCon{True{}, rest}},
                Word.and(31n, tail, Word.zero(31n)),
                Word.zero(31n),
                Laws.word_and_zero(31n, tail))
            case False{}:
              Equal.cong(Word(31n), U32,
                rest => U32{WCon{False{}, rest}},
                Word.and(31n, tail, Word.zero(31n)),
                Word.zero(31n),
                Laws.word_and_zero(31n, tail))

def Laws.shift_eighteen_bit(bit):
  match bit:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.merge_first_two_fields(wk, bk):
  +tail = Encoding.append(20n, 6n, bk, Word.zero(20n))
  Equal.cong(Word(32n), U32,
    word => U32{word},
    Word.or(32n,
      Encoding.append(26n, 6n, wk, Word.zero(26n)),
      Encoding.append(26n, 6n, Word.zero(6n), tail)),
    Encoding.append(26n, 6n, wk, tail),
    Laws.word_or_disjoint(6n, 26n, wk, tail))

def merge_third_field(+wk: Word(6n), +bk: Word(6n),
  +pc: Word(6n)) ->
  {U32.or(U32{Encoding.append(26n, 6n, wk,
      Encoding.append(20n, 6n, bk, Word.zero(20n)))},
    Encoding.field2(pc)) ==
    U32{Encoding.append(26n, 6n, wk,
      Encoding.append(20n, 6n, bk,
        Encoding.append(14n, 6n, pc,
          Word.zero(14n))))} : U32}:
  +pc_tail = Encoding.append(14n, 6n, pc, Word.zero(14n))
  +bk_tail = Encoding.append(20n, 6n, bk, Word.zero(20n))
  +incoming = Encoding.append(20n, 6n,
    Word.zero(6n), pc_tail)
  +merged_tail = Encoding.append(20n, 6n, bk, pc_tail)
  outer = Laws.word_or_into_tail(6n, 26n,
    wk, bk_tail, incoming)
  inner = Laws.word_or_disjoint(6n, 20n, bk, pc_tail)
  lifted = Equal.cong(Word(26n), Word(32n),
    tail => Encoding.append(26n, 6n, wk, tail),
    Word.or(26n, bk_tail, incoming), merged_tail, inner)
  combined = Equal.trans(Word(32n),
    Word.or(32n,
      Encoding.append(26n, 6n, wk, bk_tail),
      Encoding.append(26n, 6n, Word.zero(6n), incoming)),
    Encoding.append(26n, 6n, wk,
      Word.or(26n, bk_tail, incoming)),
    Encoding.append(26n, 6n, wk, merged_tail),
    outer, lifted)
  Equal.cong(Word(32n), U32,
    word => U32{word},
    Word.or(32n,
      Encoding.append(26n, 6n, wk, bk_tail),
      Encoding.append(26n, 6n, Word.zero(6n), incoming)),
    Encoding.append(26n, 6n, wk, merged_tail), combined)

def Laws.merge_first_three_fields(wk, bk, pc):
  +two = {U32{Encoding.append(26n, 6n, wk,
    Encoding.append(20n, 6n, bk, Word.zero(20n)))} : U32}
  lifted = Equal.cong(U32, U32,
    first => U32.or(first, Encoding.field2(pc)),
    U32.or(Encoding.square(wk), Encoding.field1(bk)),
    two, Laws.merge_first_two_fields(wk, bk))
  Equal.trans(U32,
    U32.or(U32.or(Encoding.square(wk),
      Encoding.field1(bk)), Encoding.field2(pc)),
    U32.or(two, Encoding.field2(pc)),
    U32{Encoding.append(26n, 6n, wk,
      Encoding.append(20n, 6n, bk,
        Encoding.append(14n, 6n, pc,
          Word.zero(14n))))},
    lifted, merge_third_field(wk, bk, pc))

def merge_fourth_field(+wk: Word(6n), +bk: Word(6n),
  +pc: Word(6n), +side: Bool) ->
  {U32.or(U32{Encoding.append(26n, 6n, wk,
      Encoding.append(20n, 6n, bk,
        Encoding.append(14n, 6n, pc, Word.zero(14n))))},
    Encoding.field3(side)) ==
    U32{Encoding.append(26n, 6n, wk,
      Encoding.append(20n, 6n, bk,
        Encoding.append(14n, 6n, pc,
          WCon{side, Word.zero(13n)})))} : U32}:
  +bit_tail = {WCon{side, Word.zero(13n)} : Word(14n)}
  +pc_tail = Encoding.append(14n, 6n, pc, Word.zero(14n))
  +bk_tail = Encoding.append(20n, 6n, bk, pc_tail)
  +incoming_pc = Encoding.append(14n, 6n,
    Word.zero(6n), bit_tail)
  +incoming_bk = Encoding.append(20n, 6n,
    Word.zero(6n), incoming_pc)
  +merged_pc = Encoding.append(14n, 6n, pc, bit_tail)
  +merged_bk = Encoding.append(20n, 6n, bk, merged_pc)
  outer_wk = Laws.word_or_into_tail(6n, 26n,
    wk, bk_tail, incoming_bk)
  outer_bk = Laws.word_or_into_tail(6n, 20n,
    bk, pc_tail, incoming_pc)
  inner = Laws.word_or_disjoint(6n, 14n, pc, bit_tail)
  lifted_inner = Equal.cong(Word(20n), Word(26n),
    tail => Encoding.append(20n, 6n, bk, tail),
    Word.or(20n, pc_tail, incoming_pc),
    merged_pc, inner)
  merged_inner = Equal.trans(Word(26n),
    Word.or(26n, bk_tail, incoming_bk),
    Encoding.append(20n, 6n, bk,
      Word.or(20n, pc_tail, incoming_pc)),
    merged_bk, outer_bk, lifted_inner)
  lifted_bk = Equal.cong(Word(26n), Word(32n),
    tail => Encoding.append(26n, 6n, wk, tail),
    Word.or(26n, bk_tail, incoming_bk),
    merged_bk, merged_inner)
  merged_word = Equal.trans(Word(32n),
    Word.or(32n,
      Encoding.append(26n, 6n, wk, bk_tail),
      Encoding.append(26n, 6n, Word.zero(6n), incoming_bk)),
    Encoding.append(26n, 6n, wk,
      Word.or(26n, bk_tail, incoming_bk)),
    Encoding.append(26n, 6n, wk, merged_bk),
    outer_wk, lifted_bk)
  Equal.cong(Word(32n), U32, word => U32{word},
    Word.or(32n,
      Encoding.append(26n, 6n, wk, bk_tail),
      Encoding.append(26n, 6n, Word.zero(6n), incoming_bk)),
    Encoding.append(26n, 6n, wk, merged_bk),
    merged_word)

def Laws.clean_index_is_raw(wk, bk, pc, side):
  match wk bk pc:
    case WCon{a0, WCon{a1, WCon{a2, WCon{a3,
      WCon{a4, WCon{a5, WNil{}}}}}}}
      WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WNil{}}}}}}}
      WCon{c0, WCon{c1, WCon{c2, WCon{c3,
      WCon{c4, WCon{c5, WNil{}}}}}}}:
      {==}

def Laws.merge_all_index_fields(wk, bk, pc, side):
  +three = {U32{Encoding.append(26n, 6n, wk,
    Encoding.append(20n, 6n, bk,
      Encoding.append(14n, 6n, pc,
        Word.zero(14n))))} : U32}
  lifted = Equal.cong(U32, U32,
    first => U32.or(first, Encoding.field3(side)),
    U32.or(U32.or(Encoding.square(wk),
      Encoding.field1(bk)), Encoding.field2(pc)),
    three, Laws.merge_first_three_fields(wk, bk, pc))
  first = Equal.trans(U32,
    U32.or(U32.or(U32.or(
      Encoding.square(wk), Encoding.field1(bk)),
      Encoding.field2(pc)), Encoding.field3(side)),
    U32.or(three, Encoding.field3(side)),
    U32{Encoding.append(26n, 6n, wk,
      Encoding.append(20n, 6n, bk,
        Encoding.append(14n, 6n, pc,
          WCon{side, Word.zero(13n)})))},
    lifted, merge_fourth_field(wk, bk, pc, side))
  Equal.trans(U32,
    U32.or(U32.or(U32.or(
      Encoding.square(wk), Encoding.field1(bk)),
      Encoding.field2(pc)), Encoding.field3(side)),
    U32{Encoding.append(26n, 6n, wk,
      Encoding.append(20n, 6n, bk,
        Encoding.append(14n, 6n, pc,
          WCon{side, Word.zero(13n)})))},
    Encoding.index(Encoding.square(wk),
      Encoding.square(bk), Encoding.square(pc),
      Encoding.turn(WCon{side, Word.zero(13n)})),
    first, Equal.sym(U32,
      Encoding.index(Encoding.square(wk),
        Encoding.square(bk), Encoding.square(pc),
        Encoding.turn(WCon{side, Word.zero(13n)})),
      U32{Encoding.append(26n, 6n, wk,
        Encoding.append(20n, 6n, bk,
          Encoding.append(14n, 6n, pc,
            WCon{side, Word.zero(13n)})))},
      Laws.clean_index_is_raw(wk, bk, pc, side)))

def join_prepend(+p: Nat, +m: Nat, +bit: Bool,
  pair: Word(p) & Word(m)) ->
  {Encoding.join(1n+p, m,
    Encoding.split.prepend(p, m, bit, pair)) ==
    WCon{bit, Encoding.join(p, m, pair)} :
    Word(1n+Nat.add(p, m))}:
  match pair:
    case (low, high):
      {==}

def Laws.word_append_split_inverse(n, m, word):
  match n:
    case 0n:
      {==}
    case 1n++p:
      match word:
        case WCon{+bit, +rest}:
          bridge = join_prepend(p, m, bit,
            Encoding.split(m, p, rest))
          child = Laws.word_append_split_inverse(p, m, rest)
          lifted = Equal.cong(Word(Nat.add(p, m)),
            Word(1n+Nat.add(p, m)),
            tail => WCon{bit, tail},
            Encoding.join(p, m,
              Encoding.split(m, p, rest)), rest, child)
          Equal.trans(Word(1n+Nat.add(p, m)),
            Encoding.join(1n+p, m,
              Encoding.split.prepend(p, m, bit,
                Encoding.split(m, p, rest))),
            WCon{bit, Encoding.join(p, m,
              Encoding.split(m, p, rest))},
            WCon{bit, rest}, bridge, lifted)

def and_mask_join(pair: Word(6n) & Word(26n)) ->
  {Word.and(32n,
    Encoding.join(6n, 26n, pair),
    Encoding.append(26n, 6n,
      Encoding.ones(6n), Word.zero(26n))) ==
    Encoding.append(26n, 6n,
      Encoding.low6.fin(pair), Word.zero(26n)) :
    Word(32n)}:
  match pair:
    case (+low, +high):
      +ones = Encoding.ones(6n)
      +zeros = Word.zero(26n)
      distributed = Laws.word_and_append(6n, 26n,
        low, high, ones, zeros)
      low_clean = Equal.cong(Word(6n), Word(32n),
        head => Encoding.append(26n, 6n, head,
          Word.and(26n, high, zeros)),
        Word.and(6n, low, ones), low,
        Laws.word_and_ones(6n, low))
      high_clean = Equal.cong(Word(26n), Word(32n),
        tail => Encoding.append(26n, 6n, low, tail),
        Word.and(26n, high, zeros), zeros,
        Laws.word_and_zero(26n, high))
      first = Equal.trans(Word(32n),
        Word.and(32n,
          Encoding.append(26n, 6n, low, high),
          Encoding.append(26n, 6n, ones, zeros)),
        Encoding.append(26n, 6n,
          Word.and(6n, low, ones),
          Word.and(26n, high, zeros)),
        Encoding.append(26n, 6n,
          low, Word.and(26n, high, zeros)),
        distributed, low_clean)
      Equal.trans(Word(32n),
        Word.and(32n,
          Encoding.append(26n, 6n, low, high),
          Encoding.append(26n, 6n, ones, zeros)),
        Encoding.append(26n, 6n,
          low, Word.and(26n, high, zeros)),
        Encoding.append(26n, 6n, low, zeros),
        first, high_clean)

def and_mask_join19(pair: Word(19n) & Word(13n)) ->
  {Word.and(32n,
    Encoding.join(19n, 13n, pair),
    Encoding.append(13n, 19n,
      Encoding.ones(19n), Word.zero(13n))) ==
    Encoding.append(13n, 19n,
      Encoding.low19.fin(pair), Word.zero(13n)) :
    Word(32n)}:
  match pair:
    case (+low, +high):
      +ones = Encoding.ones(19n)
      +zeros = Word.zero(13n)
      distributed = Laws.word_and_append(19n, 13n,
        low, high, ones, zeros)
      low_clean = Equal.cong(Word(19n), Word(32n),
        head => Encoding.append(13n, 19n, head,
          Word.and(13n, high, zeros)),
        Word.and(19n, low, ones), low,
        Laws.word_and_ones(19n, low))
      high_clean = Equal.cong(Word(13n), Word(32n),
        tail => Encoding.append(13n, 19n, low, tail),
        Word.and(13n, high, zeros), zeros,
        Laws.word_and_zero(13n, high))
      first = Equal.trans(Word(32n),
        Word.and(32n,
          Encoding.append(13n, 19n, low, high),
          Encoding.append(13n, 19n, ones, zeros)),
        Encoding.append(13n, 19n,
          Word.and(19n, low, ones),
          Word.and(13n, high, zeros)),
        Encoding.append(13n, 19n,
          low, Word.and(13n, high, zeros)),
        distributed, low_clean)
      Equal.trans(Word(32n),
        Word.and(32n,
          Encoding.append(13n, 19n, low, high),
          Encoding.append(13n, 19n, ones, zeros)),
        Encoding.append(13n, 19n,
          low, Word.and(13n, high, zeros)),
        Encoding.append(13n, 19n, low, zeros),
        first, high_clean)

def Laws.structural_nineteen_bit_mask_is_524287():
  {==}

def Laws.fast_mask_matches_structural_square(x):
  match x:
    case U32{+word}:
      join_eq = Laws.word_append_split_inverse(6n, 26n, word)
      replace_word = Equal.cong(Word(32n), Word(32n),
        w => Word.and(32n, w,
          Encoding.append(26n, 6n,
            Encoding.ones(6n), Word.zero(26n))),
        word, Encoding.join(6n, 26n,
          Encoding.split(26n, 6n, word)),
        Equal.sym(Word(32n),
          Encoding.join(6n, 26n,
            Encoding.split(26n, 6n, word)), word,
          join_eq))
      masked = and_mask_join(Encoding.split(26n, 6n, word))
      word_eq = Equal.trans(Word(32n),
        Word.and(32n, word,
          Encoding.append(26n, 6n,
            Encoding.ones(6n), Word.zero(26n))),
        Word.and(32n,
          Encoding.join(6n, 26n,
            Encoding.split(26n, 6n, word)),
          Encoding.append(26n, 6n,
            Encoding.ones(6n), Word.zero(26n))),
        Encoding.append(26n, 6n,
          Encoding.low6.fin(Encoding.split(26n, 6n, word)),
          Word.zero(26n)),
        replace_word, masked)
      structural = Equal.cong(Word(32n), U32,
        w => U32{w},
        Word.and(32n, word,
          Encoding.append(26n, 6n,
            Encoding.ones(6n), Word.zero(26n))),
        Encoding.append(26n, 6n,
          Encoding.low6.fin(Encoding.split(26n, 6n, word)),
          Word.zero(26n)),
        word_eq)
      numeric = Equal.cong(U32, U32,
        mask => U32.and(U32{word}, mask),
        Encoding.mask6(), 63,
        Laws.structural_six_bit_mask_is_63())
      Equal.trans(U32,
        U32.and(U32{word}, 63),
        U32.and(U32{word}, Encoding.mask6()),
        Encoding.square(Encoding.low6(U32{word})),
        Equal.sym(U32,
          U32.and(U32{word}, Encoding.mask6()),
          U32.and(U32{word}, 63), numeric),
        structural)

def truncate19_fin_as_append(pair: Word(19n) & Word(13n)) ->
  {Encoding.truncate19.fin(pair) ==
    U32{Encoding.append(13n, 19n,
      Encoding.low19.fin(pair), Word.zero(13n))} : U32}:
  match pair:
    case (low, high):
      {==}

def Laws.fast_nineteen_bit_mask_matches_truncation(i):
  match i:
    case U32{+word}:
      join_eq = Laws.word_append_split_inverse(19n, 13n, word)
      replace_word = Equal.cong(Word(32n), Word(32n),
        value => Word.and(32n, value,
          Encoding.append(13n, 19n,
            Encoding.ones(19n), Word.zero(13n))),
        word, Encoding.join(19n, 13n,
          Encoding.split(13n, 19n, word)),
        Equal.sym(Word(32n),
          Encoding.join(19n, 13n,
            Encoding.split(13n, 19n, word)), word,
          join_eq))
      masked = and_mask_join19(Encoding.split(13n, 19n, word))
      word_eq = Equal.trans(Word(32n),
        Word.and(32n, word,
          Encoding.append(13n, 19n,
            Encoding.ones(19n), Word.zero(13n))),
        Word.and(32n,
          Encoding.join(19n, 13n,
            Encoding.split(13n, 19n, word)),
          Encoding.append(13n, 19n,
            Encoding.ones(19n), Word.zero(13n))),
        Encoding.append(13n, 19n,
          Encoding.low19.fin(Encoding.split(13n, 19n, word)),
          Word.zero(13n)),
        replace_word, masked)
      structural = Equal.cong(Word(32n), U32,
        value => U32{value},
        Word.and(32n, word,
          Encoding.append(13n, 19n,
            Encoding.ones(19n), Word.zero(13n))),
        Encoding.append(13n, 19n,
          Encoding.low19.fin(Encoding.split(13n, 19n, word)),
          Word.zero(13n)),
        word_eq)
      numeric = Equal.cong(U32, U32,
        mask => U32.and(U32{word}, mask),
        Encoding.mask19(), 524287,
        Laws.structural_nineteen_bit_mask_is_524287())
      first = Equal.trans(U32,
        U32.and(U32{word}, 524287),
        U32.and(U32{word}, Encoding.mask19()),
        U32{Encoding.append(13n, 19n,
          Encoding.low19.fin(Encoding.split(13n, 19n, word)),
          Word.zero(13n))},
        Equal.sym(U32,
          U32.and(U32{word}, Encoding.mask19()),
          U32.and(U32{word}, 524287), numeric),
        structural)
      Equal.trans(U32,
        U32.and(U32{word}, 524287),
        U32{Encoding.append(13n, 19n,
          Encoding.low19.fin(Encoding.split(13n, 19n, word)),
          Word.zero(13n))},
        Encoding.truncate19(U32{word}),
        first,
        Equal.sym(U32,
          Encoding.truncate19.fin(Encoding.split(13n, 19n, word)),
          U32{Encoding.append(13n, 19n,
            Encoding.low19.fin(Encoding.split(13n, 19n, word)),
            Word.zero(13n))},
          truncate19_fin_as_append(
            Encoding.split(13n, 19n, word))))

def Laws.executable_first_square_from_packed_bits(low, high):
  +packed = {U32{Encoding.append(26n, 6n,
    low, high)} : U32}
  masked = Laws.fast_mask_matches_structural_square(packed)
  prefix = Equal.cong(Word(6n), U32,
    bits => Encoding.square(bits),
    Encoding.low6(packed), low,
    Laws.low_six_bits_of_packed_word(low, high))
  Equal.trans(U32,
    U32.and(packed, 63),
    Encoding.square(Encoding.low6(packed)),
    Encoding.square(low), masked, prefix)

def Laws.executable_second_square_from_packed_bits(low, high):
  +packed = Encoding.append(26n, 6n, low, high)
  +padded = {U32{Encoding.padn(26n, 6n, high)} : U32}
  shifted = Equal.cong(U32, U32,
    value => U32.and(value, 63),
    U32.shrn(U32{packed}, 6n), padded,
    Laws.u32_shrn_drops_six_low_bits(low, high))
  masked = Laws.fast_mask_matches_structural_square(padded)
  prefix = Equal.cong(Word(6n), U32,
    bits => Encoding.square(bits),
    Encoding.low6(padded),
    Encoding.low6.of26(Encoding.split(20n, 6n, high)),
    Laws.six_bit_prefix_survives_six_zero_pads(high))
  first = Equal.trans(U32,
    U32.and(U32.shrn(U32{packed}, 6n), 63),
    U32.and(padded, 63),
    Encoding.square(Encoding.low6(padded)),
    shifted, masked)
  Equal.trans(U32,
    U32.and(U32.shrn(U32{packed}, 6n), 63),
    Encoding.square(Encoding.low6(padded)),
    Encoding.square(
      Encoding.low6.of26(Encoding.split(20n, 6n, high))),
    first, prefix)

def Laws.executable_second_square_from_nested_fields(wk, bk, tail):
  +high = Encoding.append(20n, 6n, bk, tail)
  extracted = Laws.executable_second_square_from_packed_bits(
    wk, high)
  same = Equal.cong(Word(6n), U32,
    bits => Encoding.square(bits),
    Encoding.low6.of26(Encoding.split(20n, 6n, high)),
    bk, Laws.second_six_bits_of_nested_word(bk, tail))
  Equal.trans(U32,
    U32.and(U32.shrn(U32{Encoding.append(26n, 6n,
      wk, high)}, 6n), 63),
    Encoding.square(Encoding.low6.of26(
      Encoding.split(20n, 6n, high))),
    Encoding.square(bk), extracted, same)

def Laws.executable_third_square_from_packed_bits(low, high):
  +packed = Encoding.append(20n, 12n, low, high)
  +padded = {U32{Encoding.padn(20n, 12n, high)} : U32}
  shifted = Equal.cong(U32, U32,
    value => U32.and(value, 63),
    U32.shrn(U32{packed}, 12n), padded,
    Laws.u32_shrn_drops_twelve_low_bits(low, high))
  masked = Laws.fast_mask_matches_structural_square(padded)
  prefix = Equal.cong(Word(6n), U32,
    bits => Encoding.square(bits),
    Encoding.low6(padded),
    Encoding.low6.of20(Encoding.split(14n, 6n, high)),
    Laws.six_bit_prefix_survives_twelve_zero_pads(high))
  first = Equal.trans(U32,
    U32.and(U32.shrn(U32{packed}, 12n), 63),
    U32.and(padded, 63),
    Encoding.square(Encoding.low6(padded)),
    shifted, masked)
  Equal.trans(U32,
    U32.and(U32.shrn(U32{packed}, 12n), 63),
    Encoding.square(Encoding.low6(padded)),
    Encoding.square(
      Encoding.low6.of20(Encoding.split(14n, 6n, high))),
    first, prefix)

def Laws.executable_third_square_from_nested_fields(wk, bk, pc, tail):
  +high = Encoding.append(14n, 6n, pc, tail)
  +low = Encoding.append(6n, 6n, wk, bk)
  +nested = Encoding.append(26n, 6n, wk,
    Encoding.append(20n, 6n, bk, high))
  +regrouped = Encoding.append(20n, 12n, low, high)
  regroup = Equal.cong(Word(32n), U32,
    word => U32.and(U32.shrn(U32{word}, 12n), 63),
    nested, regrouped,
    Laws.regroup_first_two_squares(wk, bk, high))
  extracted = Laws.executable_third_square_from_packed_bits(
    low, high)
  same = Equal.cong(Word(6n), U32,
    bits => Encoding.square(bits),
    Encoding.low6.of20(Encoding.split(14n, 6n, high)),
    pc, Laws.third_six_bits_of_nested_word(pc, tail))
  first = Equal.trans(U32,
    U32.and(U32.shrn(U32{nested}, 12n), 63),
    U32.and(U32.shrn(U32{regrouped}, 12n), 63),
    Encoding.square(Encoding.low6.of20(
      Encoding.split(14n, 6n, high))),
    regroup, extracted)
  Equal.trans(U32,
    U32.and(U32.shrn(U32{nested}, 12n), 63),
    Encoding.square(Encoding.low6.of20(
      Encoding.split(14n, 6n, high))),
    Encoding.square(pc), first, same)

def Laws.executable_turn_from_packed_bits(low, side):
  +high = {WCon{side, Word.zero(13n)} : Word(14n)}
  +packed = Encoding.append(14n, 18n, low, high)
  Equal.trans(U32,
    U32.shrn(U32{packed}, 18n),
    U32{Encoding.padn(14n, 18n, high)},
    Encoding.turn(high),
    Laws.u32_shrn_drops_eighteen_low_bits(low, high),
    Equal.cong(Word(32n), U32,
      value => U32{value},
      Encoding.padn(14n, 18n, high),
      Encoding.append(18n, 14n, high, Word.zero(18n)),
      Laws.eighteen_pads_make_clean_turn(side)))

def Laws.executable_turn_from_any_packed_bits(low, high):
  +packed = Encoding.append(14n, 18n, low, high)
  Equal.trans(U32,
    U32.shrn(U32{packed}, 18n),
    U32{Encoding.padn(14n, 18n, high)},
    Encoding.turn(high),
    Laws.u32_shrn_drops_eighteen_low_bits(low, high),
    Equal.cong(Word(32n), U32,
      value => U32{value},
      Encoding.padn(14n, 18n, high),
      Encoding.append(18n, 14n, high, Word.zero(18n)),
      Laws.eighteen_pads_make_turn(high)))

def Laws.executable_turn_from_nested_fields(wk, bk, pc, side):
  +high = {WCon{side, Word.zero(13n)} : Word(14n)}
  +low = Encoding.append(12n, 6n, wk,
    Encoding.append(6n, 6n, bk, pc))
  +nested = Encoding.append(26n, 6n, wk,
    Encoding.append(20n, 6n, bk,
      Encoding.append(14n, 6n, pc, high)))
  +regrouped = Encoding.append(14n, 18n, low, high)
  regroup = Equal.cong(Word(32n), U32,
    word => U32.shrn(U32{word}, 18n),
    nested, regrouped,
    Laws.regroup_first_three_squares(wk, bk, pc, high))
  Equal.trans(U32,
    U32.shrn(U32{nested}, 18n),
    U32.shrn(U32{regrouped}, 18n),
    Encoding.turn(high),
    regroup,
    Laws.executable_turn_from_packed_bits(low, side))

def Laws.executable_turn_from_any_nested_fields(wk, bk, pc, high):
  +low = Encoding.append(12n, 6n, wk,
    Encoding.append(6n, 6n, bk, pc))
  +nested = Encoding.append(26n, 6n, wk,
    Encoding.append(20n, 6n, bk,
      Encoding.append(14n, 6n, pc, high)))
  +regrouped = Encoding.append(14n, 18n, low, high)
  regroup = Equal.cong(Word(32n), U32,
    word => U32.shrn(U32{word}, 18n),
    nested, regrouped,
    Laws.regroup_first_three_squares(wk, bk, pc, high))
  Equal.trans(U32,
    U32.shrn(U32{nested}, 18n),
    U32.shrn(U32{regrouped}, 18n),
    Encoding.turn(high),
    regroup,
    Laws.executable_turn_from_any_packed_bits(low, high))

def Laws.executable_decode_clean_index(wk, bk, pc, side):
  +turn_bits = {WCon{side, Word.zero(13n)} : Word(14n)}
  +tail20 = Encoding.append(14n, 6n, pc, turn_bits)
  +tail26 = Encoding.append(20n, 6n, bk, tail20)
  +packed = Encoding.append(26n, 6n, wk, tail26)
  +raw = {U32{packed} : U32}
  +clean_index = Encoding.index(
    Encoding.square(wk), Encoding.square(bk),
    Encoding.square(pc), Encoding.turn(turn_bits))
  +a_raw = U32.and(raw, 63)
  +b_raw = U32.and(U32.shrn(raw, 6n), 63)
  +c_raw = U32.and(U32.shrn(raw, 12n), 63)
  +d_raw = U32.shrn(raw, 18n)
  +a = Encoding.square(wk)
  +b = Encoding.square(bk)
  +c = Encoding.square(pc)
  +d = Encoding.turn(turn_bits)
  decoded = Equal.cong(U32, Rules.State,
    value => Rules.decode(value),
    clean_index, raw,
    Laws.clean_index_is_raw(wk, bk, pc, side))
  first = Equal.cong(U32, Rules.State,
    value => Rules.State{value, b_raw, c_raw, d_raw},
    a_raw, a,
    Laws.executable_first_square_from_packed_bits(wk, tail26))
  second = Equal.cong(U32, Rules.State,
    value => Rules.State{a, value, c_raw, d_raw},
    b_raw, b,
    Laws.executable_second_square_from_nested_fields(
      wk, bk, tail20))
  third = Equal.cong(U32, Rules.State,
    value => Rules.State{a, b, value, d_raw},
    c_raw, c,
    Laws.executable_third_square_from_nested_fields(
      wk, bk, pc, turn_bits))
  fourth = Equal.cong(U32, Rules.State,
    value => Rules.State{a, b, c, value},
    d_raw, d,
    Laws.executable_turn_from_nested_fields(wk, bk, pc, side))
  step1 = Equal.trans(Rules.State,
    Rules.decode(clean_index),
    Rules.State{a_raw, b_raw, c_raw, d_raw},
    Rules.State{a, b_raw, c_raw, d_raw},
    decoded, first)
  step2 = Equal.trans(Rules.State,
    Rules.decode(clean_index),
    Rules.State{a, b_raw, c_raw, d_raw},
    Rules.State{a, b, c_raw, d_raw},
    step1, second)
  step3 = Equal.trans(Rules.State,
    Rules.decode(clean_index),
    Rules.State{a, b, c_raw, d_raw},
    Rules.State{a, b, c, d_raw},
    step2, third)
  Equal.trans(Rules.State,
    Rules.decode(clean_index),
    Rules.State{a, b, c, d_raw},
    Rules.State{a, b, c, d},
    step3, fourth)

def Laws.structural_decode_packed_fields(wk, bk, pc, high):
  match wk bk pc:
    case WCon{a0, WCon{a1, WCon{a2, WCon{a3,
      WCon{a4, WCon{a5, WNil{}}}}}}}
      WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WNil{}}}}}}}
      WCon{c0, WCon{c1, WCon{c2, WCon{c3,
      WCon{c4, WCon{c5, WNil{}}}}}}}:
      {==}

def Laws.structural_chunks_pack_inverse(word):
  match word:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WCon{b6, WCon{b7,
        rest24}}}}}}}}:
      match rest24:
        case WCon{b8, WCon{b9, WCon{b10, WCon{b11,
          WCon{b12, WCon{b13, WCon{b14, WCon{b15,
            rest16}}}}}}}}:
          match rest16:
            case WCon{b16, WCon{b17, WCon{b18, WCon{b19,
              WCon{b20, WCon{b21, WCon{b22, WCon{b23,
                rest8}}}}}}}}:
              match rest8:
                case WCon{b24, WCon{b25, WCon{b26, WCon{b27,
                  WCon{b28, WCon{b29, WCon{b30, WCon{b31,
                    WNil{}}}}}}}}}:
                  {==}

def Laws.executable_decode_packed_fields(wk, bk, pc, high):
  +tail20 = Encoding.append(14n, 6n, pc, high)
  +tail26 = Encoding.append(20n, 6n, bk, tail20)
  +packed = Encoding.append(26n, 6n, wk, tail26)
  +raw = {U32{packed} : U32}
  +a_raw = U32.and(raw, 63)
  +b_raw = U32.and(U32.shrn(raw, 6n), 63)
  +c_raw = U32.and(U32.shrn(raw, 12n), 63)
  +d_raw = U32.shrn(raw, 18n)
  +a = Encoding.square(wk)
  +b = Encoding.square(bk)
  +c = Encoding.square(pc)
  +d = Encoding.turn(high)
  first = Equal.cong(U32, Rules.State,
    value => Rules.State{value, b_raw, c_raw, d_raw},
    a_raw, a,
    Laws.executable_first_square_from_packed_bits(wk, tail26))
  second = Equal.cong(U32, Rules.State,
    value => Rules.State{a, value, c_raw, d_raw},
    b_raw, b,
    Laws.executable_second_square_from_nested_fields(
      wk, bk, tail20))
  third = Equal.cong(U32, Rules.State,
    value => Rules.State{a, b, value, d_raw},
    c_raw, c,
    Laws.executable_third_square_from_nested_fields(
      wk, bk, pc, high))
  fourth = Equal.cong(U32, Rules.State,
    value => Rules.State{a, b, c, value},
    d_raw, d,
    Laws.executable_turn_from_any_nested_fields(wk, bk, pc, high))
  step1 = Equal.trans(Rules.State,
    Rules.decode(raw),
    Rules.State{a, b_raw, c_raw, d_raw},
    Rules.State{a, b, c_raw, d_raw},
    first, second)
  step2 = Equal.trans(Rules.State,
    Rules.decode(raw),
    Rules.State{a, b, c_raw, d_raw},
    Rules.State{a, b, c, d_raw},
    step1, third)
  Equal.trans(Rules.State,
    Rules.decode(raw),
    Rules.State{a, b, c, d_raw},
    Rules.State{a, b, c, d},
    step2, fourth)

def decoder_equivalence_by_parts(+word: Word(32n),
  parts: Word(6n) & Word(6n) & Word(6n) & Word(14n),
  +packed_eq: {Encoding.pack.parts(parts) == word : Word(32n)}) ->
  {Rules.decode(U32{word}) ==
    Laws.structural_state(U32{word}) : Rules.State}:
  match parts:
    case (wk, bk, pc, high):
      +wk_bits = {wk : Word(6n)}
      +bk_bits = {bk : Word(6n)}
      +pc_bits = {pc : Word(6n)}
      +high_bits = {high : Word(14n)}
      +packed = Encoding.pack(wk_bits, bk_bits, pc_bits, high_bits)
      +a = Encoding.square(wk_bits)
      +b = Encoding.square(bk_bits)
      +c = Encoding.square(pc_bits)
      +d = Encoding.turn(high_bits)
      fast_input = Equal.cong(Word(32n), Rules.State,
        value => Rules.decode(U32{value}),
        word, packed,
        Equal.sym(Word(32n), packed, word, packed_eq))
      fast_packed = Laws.executable_decode_packed_fields(
        wk_bits, bk_bits, pc_bits, high_bits)
      structural_packed = Equal.cong(
        U32 & U32 & U32 & U32, Rules.State,
        value => Laws.structural_state.fin(value),
        Encoding.decode(U32{packed}),
        {(a, b, c, d) : U32 & U32 & U32 & U32},
        Laws.structural_decode_packed_fields(
          wk_bits, bk_bits, pc_bits, high_bits))
      structural_back = Equal.cong(Word(32n), Rules.State,
        value => Laws.structural_state(U32{value}),
        packed, word, packed_eq)
      first = Equal.trans(Rules.State,
        Rules.decode(U32{word}),
        Rules.decode(U32{packed}),
        Rules.State{a, b, c, d},
        fast_input, fast_packed)
      second = Equal.trans(Rules.State,
        Rules.decode(U32{word}),
        Rules.State{a, b, c, d},
        Laws.structural_state(U32{packed}),
        first,
        Equal.sym(Rules.State,
          Laws.structural_state(U32{packed}),
          Rules.State{a, b, c, d},
          structural_packed))
      Equal.trans(Rules.State,
        Rules.decode(U32{word}),
        Laws.structural_state(U32{packed}),
        Laws.structural_state(U32{word}),
        second, structural_back)

def Laws.executable_decoder_equals_structural_decoder(i):
  match i:
    case U32{word}:
      decoder_equivalence_by_parts(word,
        Encoding.chunks(word),
        Laws.structural_chunks_pack_inverse(word))

def Laws.clean_repack_is_low_nineteen_bits(wk, bk, pc,
  side, upper):
  match wk bk pc:
    case WCon{a0, WCon{a1, WCon{a2, WCon{a3,
      WCon{a4, WCon{a5, WNil{}}}}}}}
      WCon{b0, WCon{b1, WCon{b2, WCon{b3,
      WCon{b4, WCon{b5, WNil{}}}}}}}
      WCon{c0, WCon{c1, WCon{c2, WCon{c3,
      WCon{c4, WCon{c5, WNil{}}}}}}}:
      {==}

def Laws.fast_second_field(x):
  +bits = Encoding.low6(x)
  masked = Equal.cong(U32, U32,
    value => U32.shln(value, 6n),
    U32.and(x, 63), Encoding.square(bits),
    Laws.fast_mask_matches_structural_square(x))
  Equal.trans(U32,
    U32.shln(U32.and(x, 63), 6n),
    U32.shln(Encoding.square(bits), 6n),
    Encoding.field1(bits),
    masked, Laws.shift_six_square(bits))

def Laws.fast_third_field(x):
  +bits = Encoding.low6(x)
  masked = Equal.cong(U32, U32,
    value => U32.shln(value, 12n),
    U32.and(x, 63), Encoding.square(bits),
    Laws.fast_mask_matches_structural_square(x))
  Equal.trans(U32,
    U32.shln(U32.and(x, 63), 12n),
    U32.shln(Encoding.square(bits), 12n),
    Encoding.field2(bits),
    masked, Laws.shift_twelve_square(bits))

def Laws.fast_turn_field(x):
  +bit = Encoding.low1(x)
  masked = Equal.cong(U32, U32,
    value => U32.shln(value, 18n),
    U32.and(x, 1),
    U32{WCon{bit, Word.zero(31n)}},
    Laws.fast_turn_mask_matches_structural_bit(x))
  Equal.trans(U32,
    U32.shln(U32.and(x, 1), 18n),
    U32.shln(U32{WCon{bit, Word.zero(31n)}}, 18n),
    Encoding.field3(bit),
    masked, Laws.shift_eighteen_bit(bit))

def Laws.fast_index_matches_clean_structural(wk, bk, pc, side):
  +raw_a = U32.and(wk, 63)
  +raw_b = U32.shln(U32.and(bk, 63), 6n)
  +raw_c = U32.shln(U32.and(pc, 63), 12n)
  +raw_d = U32.shln(U32.and(side, 1), 18n)
  +clean_a = Encoding.square(Encoding.low6(wk))
  +clean_b = Encoding.field1(Encoding.low6(bk))
  +clean_c = Encoding.field2(Encoding.low6(pc))
  +clean_d = Encoding.field3(Encoding.low1(side))
  step_a = Equal.cong(U32, U32,
    value => U32.or(U32.or(U32.or(value, raw_b), raw_c), raw_d),
    raw_a, clean_a,
    Laws.fast_mask_matches_structural_square(wk))
  step_b = Equal.cong(U32, U32,
    value => U32.or(U32.or(U32.or(clean_a, value), raw_c), raw_d),
    raw_b, clean_b, Laws.fast_second_field(bk))
  step_c = Equal.cong(U32, U32,
    value => U32.or(U32.or(U32.or(clean_a, clean_b), value), raw_d),
    raw_c, clean_c, Laws.fast_third_field(pc))
  step_d = Equal.cong(U32, U32,
    value => U32.or(U32.or(U32.or(clean_a, clean_b), clean_c), value),
    raw_d, clean_d, Laws.fast_turn_field(side))
  part_a = Equal.trans(U32,
    U32.or(U32.or(U32.or(raw_a, raw_b), raw_c), raw_d),
    U32.or(U32.or(U32.or(clean_a, raw_b), raw_c), raw_d),
    U32.or(U32.or(U32.or(clean_a, clean_b), raw_c), raw_d),
    step_a, step_b)
  part_b = Equal.trans(U32,
    U32.or(U32.or(U32.or(raw_a, raw_b), raw_c), raw_d),
    U32.or(U32.or(U32.or(clean_a, clean_b), raw_c), raw_d),
    U32.or(U32.or(U32.or(clean_a, clean_b), clean_c), raw_d),
    part_a, step_c)
  part_c = Equal.trans(U32,
    U32.or(U32.or(U32.or(raw_a, raw_b), raw_c), raw_d),
    U32.or(U32.or(U32.or(clean_a, clean_b), clean_c), raw_d),
    U32.or(U32.or(U32.or(clean_a, clean_b), clean_c), clean_d),
    part_b, step_d)
  Equal.trans(U32,
    U32.or(U32.or(U32.or(raw_a, raw_b), raw_c), raw_d),
    U32.or(U32.or(U32.or(clean_a, clean_b), clean_c), clean_d),
    Encoding.index(
      Encoding.square(Encoding.low6(wk)),
      Encoding.square(Encoding.low6(bk)),
      Encoding.square(Encoding.low6(pc)),
      Encoding.turn(WCon{Encoding.low1(side),
        Word.zero(13n)})),
    part_c, Laws.merge_all_index_fields(
      Encoding.low6(wk), Encoding.low6(bk),
      Encoding.low6(pc), Encoding.low1(side)))

def Laws.structural_index_decode_roundtrip(wk, bk, pc, turn):
  +a = Encoding.low6(wk)
  +b = Encoding.low6(bk)
  +c = Encoding.low6(pc)
  +t = {WCon{Encoding.low1(turn), Word.zero(13n)} : Word(14n)}
  +tail20 = Encoding.append(14n, 6n, c, t)
  +tail26 = Encoding.append(20n, 6n, b, tail20)
  +packed = Encoding.append(26n, 6n, a, tail26)
  first = Equal.cong(Word(6n) & Word(26n),
    U32 & U32 & U32 & U32,
    pair => Encoding.decode.wk(pair),
    Encoding.split(26n, 6n, packed),
    (a, tail26),
    Laws.word_split_append_inverse(6n, 26n, a, tail26))
  second = Equal.cong(Word(6n) & Word(20n),
    U32 & U32 & U32 & U32,
    pair => Encoding.decode.bk(a, pair),
    Encoding.split(20n, 6n, tail26),
    (b, tail20),
    Laws.word_split_append_inverse(6n, 20n, b, tail20))
  third = Equal.cong(Word(6n) & Word(14n),
    U32 & U32 & U32 & U32,
    pair => Encoding.decode.pc(a, b, pair),
    Encoding.split(14n, 6n, tail20),
    (c, t),
    Laws.word_split_append_inverse(6n, 14n, c, t))
  first_two = Equal.trans(U32 & U32 & U32 & U32,
    Encoding.decode.wk(Encoding.split(26n, 6n, packed)),
    Encoding.decode.bk(a,
      Encoding.split(20n, 6n, tail26)),
    Encoding.decode.bk(a, (b, tail20)), first, second)
  Equal.trans(U32 & U32 & U32 & U32,
    Encoding.decode.wk(Encoding.split(26n, 6n, packed)),
    Encoding.decode.pc(a, b,
      Encoding.split(14n, 6n, tail20)),
    (Encoding.square(a), Encoding.square(b),
      Encoding.square(c), Encoding.turn(t)),
    first_two, third)

def Laws.structural_square_roundtrip(bits):
  %Laws.word_split_append_inverse(6n, 26n, bits,
    Word.zero(26n)) :
    {Encoding.low6.fin(Encoding.split(26n, 6n,
      Encoding.append(26n, 6n, bits, Word.zero(26n)))) ==
      Encoding.low6.fin(_) : Word(6n)}
  {==}

def Laws.structural_turn_bit_roundtrip(bit):
  {==}

def Laws.clean_structural_index_is_index(wk, bk, pc, side):
  +a = Encoding.low6(wk)
  +b = Encoding.low6(bk)
  +c = Encoding.low6(pc)
  +t = {WCon{Encoding.low1(side),
    Word.zero(13n)} : Word(14n)}
  +aa = Encoding.low6(Encoding.square(a))
  +bb = Encoding.low6(Encoding.square(b))
  +cc = Encoding.low6(Encoding.square(c))
  +tail0 = Encoding.append(20n, 6n, bb,
    Encoding.append(14n, 6n, cc, t))
  +tail1 = Encoding.append(14n, 6n, cc, t)
  +tail2 = Encoding.append(14n, 6n, c, t)
  step_a = Equal.cong(Word(6n), U32,
    value => U32{Encoding.append(26n, 6n, value, tail0)},
    aa, a, Laws.structural_square_roundtrip(a))
  step_b = Equal.cong(Word(6n), U32,
    value => U32{Encoding.append(26n, 6n, a,
      Encoding.append(20n, 6n, value, tail1))},
    bb, b, Laws.structural_square_roundtrip(b))
  step_c = Equal.cong(Word(6n), U32,
    value => U32{Encoding.append(26n, 6n, a,
      Encoding.append(20n, 6n, b,
        Encoding.append(14n, 6n, value, t)))},
    cc, c, Laws.structural_square_roundtrip(c))
  first = Equal.trans(U32,
    U32{Encoding.append(26n, 6n, aa, tail0)},
    U32{Encoding.append(26n, 6n, a, tail0)},
    U32{Encoding.append(26n, 6n, a,
      Encoding.append(20n, 6n, b, tail1))},
    step_a, step_b)
  Equal.trans(U32,
    U32{Encoding.append(26n, 6n, aa, tail0)},
    U32{Encoding.append(26n, 6n, a,
      Encoding.append(20n, 6n, b, tail1))},
    U32{Encoding.append(26n, 6n, a,
      Encoding.append(20n, 6n, b, tail2))},
    first, step_c)

def Laws.executable_index_equals_structural_index(wk, bk, pc, side):
  Equal.trans(U32,
    Rules.index(Rules.State{wk, bk, pc, side}),
    Encoding.index(
      Encoding.square(Encoding.low6(wk)),
      Encoding.square(Encoding.low6(bk)),
      Encoding.square(Encoding.low6(pc)),
      Encoding.turn(WCon{Encoding.low1(side),
        Word.zero(13n)})),
    Encoding.index(wk, bk, pc, side),
    Laws.fast_index_matches_clean_structural(wk, bk, pc, side),
    Laws.clean_structural_index_is_index(wk, bk, pc, side))

def Laws.executable_repack_of_packed_word_is_low_nineteen_bits(
  wk, bk, pc, high):
  match high:
    case WCon{side, upper}:
      +turn_bits = {WCon{side, upper} : Word(14n)}
      +raw = {U32{Encoding.pack(wk, bk, pc,
        turn_bits)} : U32}
      +a = Encoding.square(wk)
      +b = Encoding.square(bk)
      +c = Encoding.square(pc)
      +d = Encoding.turn(turn_bits)
      decoded = Equal.cong(Rules.State, U32,
        state => Rules.index(state),
        Rules.decode(raw), Rules.State{a, b, c, d},
        Laws.executable_decode_packed_fields(
          wk, bk, pc, turn_bits))
      encoded = Laws.executable_index_equals_structural_index(
        a, b, c, d)
      first = Equal.trans(U32,
        Rules.index(Rules.decode(raw)),
        Rules.index(Rules.State{a, b, c, d}),
        Encoding.index(a, b, c, d),
        decoded, encoded)
      Equal.trans(U32,
        Rules.index(Rules.decode(raw)),
        Encoding.index(a, b, c, d),
        Encoding.truncate19(raw),
        first,
        Laws.clean_repack_is_low_nineteen_bits(
          wk, bk, pc, side, upper))

def repack_by_parts(+word: Word(32n),
  parts: Word(6n) & Word(6n) & Word(6n) & Word(14n),
  +packed_eq: {Encoding.pack.parts(parts) == word : Word(32n)}) ->
  {Rules.index(Rules.decode(U32{word})) ==
    Encoding.truncate19(U32{word}) : U32}:
  match parts:
    case (wk, bk, pc, high):
      +wk_bits = {wk : Word(6n)}
      +bk_bits = {bk : Word(6n)}
      +pc_bits = {pc : Word(6n)}
      +high_bits = {high : Word(14n)}
      +packed = Encoding.pack(wk_bits, bk_bits, pc_bits,
        high_bits)
      first = Equal.cong(Word(32n), U32,
        value => Rules.index(Rules.decode(U32{value})),
        word, packed,
        Equal.sym(Word(32n), packed, word, packed_eq))
      middle = Laws.executable_repack_of_packed_word_is_low_nineteen_bits(
        wk_bits, bk_bits, pc_bits, high_bits)
      last = Equal.cong(Word(32n), U32,
        value => Encoding.truncate19(U32{value}),
        packed, word, packed_eq)
      first_two = Equal.trans(U32,
        Rules.index(Rules.decode(U32{word})),
        Rules.index(Rules.decode(U32{packed})),
        Encoding.truncate19(U32{packed}),
        first, middle)
      Equal.trans(U32,
        Rules.index(Rules.decode(U32{word})),
        Encoding.truncate19(U32{packed}),
        Encoding.truncate19(U32{word}),
        first_two, last)

def Laws.executable_repack_keeps_low_nineteen_bits(i):
  match i:
    case U32{word}:
      repack_by_parts(word, Encoding.chunks(word),
        Laws.structural_chunks_pack_inverse(word))

def Laws.executable_repack_is_nineteen_bit_mask(i):
  Equal.trans(U32,
    Rules.index(Rules.decode(i)),
    Encoding.truncate19(i),
    U32.and(i, 524287),
    Laws.executable_repack_keeps_low_nineteen_bits(i),
    Equal.sym(U32,
      U32.and(i, 524287), Encoding.truncate19(i),
      Laws.fast_nineteen_bit_mask_matches_truncation(i)))

def Laws.executable_decode_index_is_canonical(wk, bk, pc, side):
  +a = Encoding.low6(wk)
  +b = Encoding.low6(bk)
  +c = Encoding.low6(pc)
  +bit = Encoding.low1(side)
  +turn_bits = {WCon{bit, Word.zero(13n)} : Word(14n)}
  +actual_index = Rules.index(Rules.State{wk, bk, pc, side})
  +structural_index = Encoding.index(wk, bk, pc, side)
  +clean_index = Encoding.index(
    Encoding.square(a), Encoding.square(b),
    Encoding.square(c), Encoding.turn(turn_bits))
  first = Equal.cong(U32, Rules.State,
    value => Rules.decode(value),
    actual_index, structural_index,
    Laws.executable_index_equals_structural_index(
      wk, bk, pc, side))
  second = Equal.cong(U32, Rules.State,
    value => Rules.decode(value),
    structural_index, clean_index,
    Equal.sym(U32, clean_index, structural_index,
      Laws.clean_structural_index_is_index(
        wk, bk, pc, side)))
  first_two = Equal.trans(Rules.State,
    Rules.decode(actual_index),
    Rules.decode(structural_index),
    Rules.decode(clean_index), first, second)
  Equal.trans(Rules.State,
    Rules.decode(actual_index),
    Rules.decode(clean_index),
    Rules.State{Encoding.square(a), Encoding.square(b),
      Encoding.square(c), Encoding.turn(turn_bits)},
    first_two,
    Laws.executable_decode_clean_index(a, b, c, bit))

def Laws.three_man_slot_count():
  {==}

def Laws.nat_add_associative(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Laws.nat_add_associative(p, b, c) :
        {1n+Nat.add(Nat.add(p, b), c) ==
          1n+_ : Nat}
      {==}

def Laws.nat_add_right_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Laws.nat_add_right_zero(p) :
        {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def Laws.nat_add_succ_right(a, b):
  match a:
    case 0n:
      {==}
    case 1n+rest:
      Equal.cong(Nat, Nat,
        value => 1n+value,
        Nat.add(rest, 1n+b),
        1n+Nat.add(rest, b),
        Laws.nat_add_succ_right(rest, b))

def proof_tree_bytes_length_go(
  n: Nat, +tree: ProofTree.Tree,
  full: ProofTree.Full(n, tree),
  +acc: List<&2, U32>) ->
  {List.length(&2, U32,
      ProofTree.bytes.go(tree, acc)) ==
    Nat.add(Laws.nat_power_of_two(n),
      List.length(&2, U32,
        acc)) : Nat}:
  match n tree full:
    case 0n ProofTree.Leaf{value}
         proof:
      {==}
    case 0n ProofTree.Node{left, right}
         impossible:
      match impossible:
    case 1n++rest ProofTree.Leaf{value}
         impossible:
      match impossible:
    case 1n++rest ProofTree.Node{left, right}
         pair:
      match pair:
        case (left_full, right_full):
          +size = Laws.nat_power_of_two(rest)
          +right_bytes =
            ProofTree.bytes.go(right, acc)
          +acc_length = List.length(&2,
            U32, acc)
          +right_length = List.length(&2,
            U32, right_bytes)
          first = proof_tree_bytes_length_go(
            rest, left, left_full,
            right_bytes)
          second = proof_tree_bytes_length_go(
            rest, right, right_full,
            acc)
          Equal.trans(Nat,
            List.length(&2, U32,
              ProofTree.bytes.go(tree,
                acc)),
            Nat.add(size, right_length),
            Nat.add(
              Laws.nat_power_of_two(
                1n+rest),
              acc_length),
            first,
            Equal.trans(Nat,
              Nat.add(size, right_length),
              Nat.add(size,
                Nat.add(size,
                  acc_length)),
              Nat.add(Nat.add(size,
                size), acc_length),
              Equal.cong(Nat, Nat,
                value => Nat.add(size,
                  value),
                right_length,
                Nat.add(size,
                  acc_length), second),
              Equal.sym(Nat,
                Nat.add(Nat.add(size,
                  size), acc_length),
                Nat.add(size,
                  Nat.add(size,
                    acc_length)),
                Laws.nat_add_associative(
                  size, size,
                  acc_length))))

def Laws.proof_tree_bytes_length(n,
  tree, full):
  Equal.trans(Nat,
    List.length(&2, U32,
      ProofTree.bytes(tree)),
    Nat.add(
      Laws.nat_power_of_two(n),
      0n),
    Laws.nat_power_of_two(n),
    proof_tree_bytes_length_go(n,
      tree, full, Nil{}),
    Laws.nat_add_right_zero(
      Laws.nat_power_of_two(n)))

def proof_tree_bytes_skip(
  n: Nat, +tree: ProofTree.Tree,
  full: ProofTree.Full(n, tree),
  +acc: List<&2, U32>,
  +index: Nat) ->
  {List.get(&2, U32,
      ProofTree.bytes.go(tree, acc),
      Nat.add(ProofTree.slot_count(n),
        index)) ==
    List.get(&2, U32, acc,
      index) : Maybe<&2, U32>}:
  match n tree full:
    case 0n ProofTree.Leaf{value}
         proof:
      {==}
    case 0n ProofTree.Node{left, right}
         impossible:
      match impossible:
    case 1n++rest ProofTree.Leaf{value}
         impossible:
      match impossible:
    case 1n++rest ProofTree.Node{left, right}
         pair:
      match pair:
        case (left_full, right_full):
          +size = ProofTree.slot_count(rest)
          +right_bytes =
            ProofTree.bytes.go(right,
              acc)
          +middle_index = Nat.add(size,
            index)
          +start_index = Nat.add(
            Nat.add(size, size),
            index)
          +middle = List.get(&2,
            U32,
            ProofTree.bytes.go(left,
              right_bytes),
            Nat.add(size,
              middle_index))
          +after_left = List.get(&2,
            U32, right_bytes,
            middle_index)
          Equal.trans(Maybe<&2, U32>,
            List.get(&2, U32,
              ProofTree.bytes.go(tree,
                acc), start_index),
            middle,
            List.get(&2, U32, acc,
              index),
            Equal.cong(Nat,
              Maybe<&2, U32>,
              at => List.get(&2,
                U32,
                ProofTree.bytes.go(tree,
                  acc), at),
              start_index,
              Nat.add(size,
                middle_index),
              Laws.nat_add_associative(
                size, size, index)),
            Equal.trans(Maybe<&2,
              U32>, middle,
              after_left,
              List.get(&2, U32,
                acc, index),
              proof_tree_bytes_skip(
                rest, left,
                left_full, right_bytes,
                middle_index),
              proof_tree_bytes_skip(
                rest, right,
                right_full, acc,
                index)))

def proof_tree_bytes_go_at_path(
  n: Nat, +tree: ProofTree.Tree,
  full: ProofTree.Full(n, tree),
  +bits: Word(n),
  +acc: List<&2, U32>) ->
  {List.get(&2, U32,
      ProofTree.bytes.go(tree, acc),
      ProofTree.byte_offset(n,
        bits)) ==
    Some{ProofTree.get(n,
      tree, bits)} : Maybe<&2,
      U32>}:
  match n tree full bits:
    case 0n ProofTree.Leaf{value}
         proof WNil{}:
      {==}
    case 0n ProofTree.Node{left, right}
         impossible WNil{}:
      Empty.absurd(
        {List.get(&2, U32,
          ProofTree.bytes.go(
            ProofTree.Node{left,
              right}, acc),
          ProofTree.byte_offset(0n,
            WNil{})) ==
          Some{ProofTree.get(0n,
            ProofTree.Node{left,
              right}, WNil{})} :
          Maybe<&2, U32>},
        impossible)
    case 1n++rest ProofTree.Leaf{value}
         impossible WCon{bit, tail}:
      Empty.absurd(
        {List.get(&2, U32,
          ProofTree.bytes.go(
            ProofTree.Leaf{value},
            acc),
          ProofTree.byte_offset(
            1n+rest,
            WCon{bit, tail})) ==
          Some{ProofTree.get(
            1n+rest,
            ProofTree.Leaf{value},
            WCon{bit, tail})} :
          Maybe<&2, U32>},
        impossible)
    case 1n++rest ProofTree.Node{left,
         right} Tuple{left_full, right_full}
         WCon{False{}, tail}:
      proof_tree_bytes_go_at_path(
        rest, left,
        left_full, tail,
        ProofTree.bytes.go(right,
          acc))
    case 1n++rest ProofTree.Node{left,
         right} Tuple{left_full, right_full}
         WCon{True{}, tail}:
      +right_bytes =
        ProofTree.bytes.go(right,
          acc)
      +offset = ProofTree.byte_offset(
        rest, tail)
      Equal.trans(Maybe<&2, U32>,
        List.get(&2, U32,
          ProofTree.bytes.go(tree,
            acc),
          Nat.add(
            ProofTree.slot_count(
              rest), offset)),
        List.get(&2, U32,
          right_bytes, offset),
        Some{ProofTree.get(rest,
          right, tail)},
        proof_tree_bytes_skip(
          rest, left,
          left_full, right_bytes,
          offset),
        proof_tree_bytes_go_at_path(
          rest, right,
          right_full, tail, acc))

def Laws.proof_tree_byte_at_path(
  n, tree, full, bits):
  proof_tree_bytes_go_at_path(
    n, tree, full, bits,
    Nil{})

def Laws.clock_before_positive_budget(clock,
  rest):
  match clock:
    case 0n:
      Unit{}
    case 1n+earlier:
      Laws.clock_before_positive_budget(
        earlier, rest)

def Laws.clock_budget_implies_before_hundred(
  clock, rest, budget):
  equality_cast(Nat,
    limit => Laws.Truth(Nat.is_lt(
      clock, limit)),
    Nat.add(clock, 1n+rest),
    100n, budget,
    Laws.clock_before_positive_budget(
      clock, rest))

def uniform_array_bytes_length_go(d: Nat, +value: U32,
  +acc: List<&2, U32>) ->
  {List.length(&2, U32, Output.bytes.go(
    Array.new(U32, d, value), acc)) ==
    Nat.add(Laws.nat_power_of_two(d),
      List.length(&2, U32, acc)) : Nat}:
  match d:
    case 0n:
      {==}
    case 1n++p:
      +count = Laws.nat_power_of_two(p)
      +prior_count = List.length(&2, U32, acc)
      +right = Output.bytes.go(
        Array.new(U32, p, value), acc)
      +right_count = List.length(&2, U32, right)
      right_length = uniform_array_bytes_length_go(
        p, value, acc)
      left_length = uniform_array_bytes_length_go(
        p, value, right)
      bridge = Equal.cong(Nat, Nat,
        n => Nat.add(count, n),
        right_count, Nat.add(count, prior_count),
        right_length)
      middle = Equal.trans(Nat,
        List.length(&2, U32, Output.bytes.go(
          Array.new(U32, p, value), right)),
        Nat.add(count, right_count),
        Nat.add(count, Nat.add(count, prior_count)),
        left_length, bridge)
      associativity = Laws.nat_add_associative(
        count, count, prior_count)
      Equal.trans(Nat,
        List.length(&2, U32, Output.bytes.go(
          Array.new(U32, p, value), right)),
        Nat.add(count, Nat.add(count, prior_count)),
        Nat.add(Nat.add(count, count), prior_count),
        middle,
        Equal.sym(Nat,
          Nat.add(Nat.add(count, count), prior_count),
          Nat.add(count, Nat.add(count, prior_count)),
          associativity))

def Laws.uniform_array_serialized_length(d, value):
  proof = uniform_array_bytes_length_go(d, value, Nil{})
  Equal.trans(Nat,
    List.length(&2, U32, Output.bytes(
      Array.new(U32, d, value))),
    Nat.add(Laws.nat_power_of_two(d), 0n),
    Laws.nat_power_of_two(d),
    proof,
    Laws.nat_add_right_zero(Laws.nat_power_of_two(d)))

def array_value_swap_lo(ys: Array<U32>,
  read: Array<U32> & U32) ->
  {Laws.array_value(Array.swap.lo(U32, ys, read)) ==
    Laws.array_value(read) : U32}:
  match read:
    case (array, value):
      {==}

def array_value_swap_hi(xs: Array<U32>,
  read: Array<U32> & U32) ->
  {Laws.array_value(Array.swap.hi(U32, xs, read)) ==
    Laws.array_value(read) : U32}:
  match read:
    case (array, value):
      {==}

def array_value_swap_lo_sound(ys: Array<U32>,
  read: Array<U32> & U32, +target: U32,
  child: {Laws.array_value(read) == target : U32}) ->
  {Laws.array_value(Array.swap.lo(U32, ys, read)) ==
    target : U32}:
  Equal.trans(U32,
    Laws.array_value(Array.swap.lo(U32, ys, read)),
    Laws.array_value(read), target,
    array_value_swap_lo(ys, read), child)

def array_value_swap_hi_sound(xs: Array<U32>,
  read: Array<U32> & U32, +target: U32,
  child: {Laws.array_value(read) == target : U32}) ->
  {Laws.array_value(Array.swap.hi(U32, xs, read)) ==
    target : U32}:
  Equal.trans(U32,
    Laws.array_value(Array.swap.hi(U32, xs, read)),
    Laws.array_value(read), target,
    array_value_swap_hi(xs, read), child)

def uniform_array_get_if(d: Nat, +value: U32,
  +h: U32, +i: U32, z: Bool) ->
  {Laws.array_value(Array.get.if(U32,
    Array.new(U32, d, value),
    Array.new(U32, d, value), h, i, z)) ==
    value : U32}:
  match d z:
    case 0n True{}:
      {==}
    case 0n False{}:
      {==}
    case 1n++p True{}:
      +half = U32.shr(h)
      array_value_swap_lo_sound(
        Array.new(U32, 1n+p, value),
        Array.get.if(U32,
          Array.new(U32, p, value),
          Array.new(U32, p, value), half, i,
          U32.is_lt(i, half)), value,
        uniform_array_get_if(p, value, half, i,
          U32.is_lt(i, half)))
    case 1n++p False{}:
      +j = U32.sub(i, h)
      +half = U32.shr(h)
      array_value_swap_hi_sound(
        Array.new(U32, 1n+p, value),
        Array.get.if(U32,
          Array.new(U32, p, value),
          Array.new(U32, p, value), half, j,
          U32.is_lt(j, half)), value,
        uniform_array_get_if(p, value, half, j,
          U32.is_lt(j, half)))

def Laws.uniform_array_get_go(d, value, n, i):
  match d:
    case 0n:
      {==}
    case 1n+p:
      +half = U32.shr(n)
      uniform_array_get_if(p, value, half, i,
        U32.is_lt(i, half))

def Laws.uniform_array_get(d, value, i):
  +size = Laws.u32_power_of_two(d)
  size_eq = Laws.uniform_array_size(d, value)
  get_eq = Equal.cong(Array<U32> & U32, U32,
    pair => Laws.array_value(Array.get.at(U32, i, pair)),
    Array.size(U32, Array.new(U32, d, value)),
    (Array.new(U32, d, value), size), size_eq)
  child = Laws.uniform_array_get_go(d, value, size,
    U32.and(i, U32.sub(size, 1)))
  Equal.trans(U32,
    Laws.array_value(Array.get(U32,
      Array.new(U32, d, value), i)),
    Laws.array_value(Array.get.go(U32,
      Array.new(U32, d, value), size,
      U32.and(i, U32.sub(size, 1)))),
    value, get_eq, child)

def uniform_zero_bytes_go(d: Nat,
  +acc: List<&2, U32>,
  prior: Laws.Truth(Laws.all_zero_bytes(acc))) ->
  Laws.Truth(Laws.all_zero_bytes(Output.bytes.go(
    Array.new(U32, d, 0), acc))):
  match d:
    case 0n:
      and_intro(U32.is_eq(0, 0),
        Laws.all_zero_bytes(acc), Unit{}, prior)
    case 1n++p:
      right = uniform_zero_bytes_go(p, acc, prior)
      uniform_zero_bytes_go(p,
        Output.bytes.go(Array.new(U32, p, 0), acc), right)

def Laws.uniform_zero_array_serializes_to_zero_values(d):
  uniform_zero_bytes_go(d, Nil{}, Unit{})

def word_cmp_reflexive(n: Nat, +w: Word(n)) ->
  {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match b:
            case False{}:
              %word_cmp_reflexive(p, t) :
                {Word.cmp.fin(False{}, False{}, Word.cmp(p, t, t)) ==
                  Word.cmp.fin(False{}, False{}, _) : Cmp}
              {==}
            case True{}:
              %word_cmp_reflexive(p, t) :
                {Word.cmp.fin(True{}, True{}, Word.cmp(p, t, t)) ==
                  Word.cmp.fin(True{}, True{}, _) : Cmp}
              {==}

def same_head_preserves_equal(+bit: Bool, +tail: Cmp,
  equal: Laws.Truth(Cmp.is_eq(tail))) ->
  Laws.Truth(Cmp.is_eq(Word.cmp.fin(bit, bit, tail))):
  match bit tail:
    case False{} LT{}:
      equal
    case True{} LT{}:
      equal
    case False{} EQ{}:
      Unit{}
    case True{} EQ{}:
      Unit{}
    case False{} GT{}:
      equal
    case True{} GT{}:
      equal

def word_cmp_is_equal(n: Nat, +w: Word(n)) ->
  Laws.Truth(Cmp.is_eq(Word.cmp(n, w, w))):
  match n:
    case 0n:
      match w:
        case WNil{}:
          Unit{}
    case 1n++p:
      match w:
        case WCon{b, +t}:
          same_head_preserves_equal(b, Word.cmp(p, t, t),
            word_cmp_is_equal(p, t))

def Laws.u32_equality_reflexive(x):
  match x:
    case U32{w}:
      word_cmp_is_equal(32n, w)

def cmp_equal_decompose(-R: Type, +a: Bool, +b: Bool,
  +tail: Cmp,
  equal: Laws.Truth(Cmp.is_eq(Word.cmp.fin(a, b, tail))),
  continue: Laws.Truth(Cmp.is_eq(tail)) ->
    {a == b : Bool} -> R) -> R:
  match a b tail:
    case _ _ LT{}:
      Empty.absurd(R, equal)
    case _ _ GT{}:
      Empty.absurd(R, equal)
    case False{} False{} EQ{}:
      continue(Unit{}, {==})
    case False{} True{} EQ{}:
      Empty.absurd(R, equal)
    case True{} False{} EQ{}:
      Empty.absurd(R, equal)
    case True{} True{} EQ{}:
      continue(Unit{}, {==})

def word_cmp_equality_reflect(n: Nat, +a: Word(n), +b: Word(n),
  equal: Laws.Truth(Cmp.is_eq(Word.cmp(n, a, b)))) ->
  {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n++p:
      match a b:
        case WCon{+ah, +at} WCon{+bh, +bt}:
          cmp_equal_decompose(
            {WCon{ah, at} == WCon{bh, bt} : Word(1n+p)},
            ah, bh, Word.cmp(p, at, bt), equal,
            tail_equal => head_equal =>
              tail_eq = word_cmp_equality_reflect(p, at, bt,
                tail_equal)
              first = Equal.cong(Word(p), Word(1n+p),
                w => WCon{ah, w}, at, bt, tail_eq)
              second = Equal.cong(Bool, Word(1n+p),
                h => WCon{h, bt}, ah, bh, head_equal)
              Equal.trans(Word(1n+p), WCon{ah, at},
                WCon{ah, bt}, WCon{bh, bt}, first, second))

def Laws.word_cmp_zero_eq_implies_zero(n, word, equal):
  word_cmp_equality_reflect(n, word, Word.zero(n), equal)

def Laws.word_lt_one_is_zero(n, word, less):
  match n:
    case 0n:
      match word:
        case WNil{}:
          Empty.absurd({WNil{} == WNil{} : Word(0n)}, less)
    case 1n++p:
      match word:
        case WCon{bit, tail}:
          match bit:
            case False{}:
              tail_equal = pair_left(
                Laws.Truth(Cmp.is_eq(
                  Word.cmp(p, tail, Word.zero(p)))),
                Laws.Truth(Bool.not(False{})),
                cmp_fin_one_lt_requires_zero_tail(False{},
                  Word.cmp(p, tail, Word.zero(p)),
                  Laws.word_cmp_zero_not_lt(p, tail), less))
              Equal.cong(Word(p), Word(1n+p),
                rest => WCon{False{}, rest},
                tail, Word.zero(p),
                Laws.word_cmp_zero_eq_implies_zero(
                  p, tail, tail_equal))
            case True{}:
              bit_zero = pair_right(
                Laws.Truth(Cmp.is_eq(
                  Word.cmp(p, tail, Word.zero(p)))),
                Laws.Truth(Bool.not(True{})),
                cmp_fin_one_lt_requires_zero_tail(True{},
                  Word.cmp(p, tail, Word.zero(p)),
                  Laws.word_cmp_zero_not_lt(p, tail), less))
              Empty.absurd(
                {WCon{True{}, tail} ==
                  Word.zero(1n+p) : Word(1n+p)},
                bit_zero)

def canonical_under64_pair(+word: Word(32n),
  pair: Word(6n) & Word(26n),
  +join_eq: {Encoding.join(6n, 26n, pair) == word : Word(32n)},
  less: Laws.Truth(U32.is_lt(U32{word}, 64))) ->
  {Encoding.square(Encoding.low6.fin(pair)) ==
    U32{word} : U32}:
  match pair:
    case (+low, +high):
      +joined = Encoding.append(26n, 6n, low, high)
      +limit = {U32{Encoding.append(26n, 6n,
        Word.zero(6n), Encoding.one(26n))} : U32}
      word_to_joined = Equal.sym(Word(32n),
        joined, word, join_eq)
      lt_word_to_joined = Equal.cong(Word(32n), Bool,
        value => U32.is_lt(U32{value}, 64),
        word, joined, word_to_joined)
      less_joined = equality_cast(Bool, Laws.Truth,
        U32.is_lt(U32{word}, 64),
        U32.is_lt(U32{joined}, 64),
        lt_word_to_joined, less)
      lt_limit = Equal.cong(U32, Bool,
        value => U32.is_lt(U32{joined}, value),
        64, limit,
        Equal.sym(U32, limit, 64,
          Laws.structural_sixty_four_is_64()))
      less_structural = equality_cast(Bool, Laws.Truth,
        U32.is_lt(U32{joined}, 64),
        U32.is_lt(U32{joined}, limit),
        lt_limit, less_joined)
      cmp_eq = Laws.word_cmp_append_zero_prefix(
        6n, 26n, low, high, Encoding.one(26n))
      cmp_lt = Equal.cong(Cmp, Bool,
        value => Cmp.is_lt(value),
        Word.cmp(32n, joined,
          Encoding.append(26n, 6n,
            Word.zero(6n), Encoding.one(26n))),
        Encoding.cmp_low_zero(6n, low,
          Word.cmp(26n, high, Encoding.one(26n))),
        cmp_eq)
      less_low = equality_cast(Bool, Laws.Truth,
        U32.is_lt(U32{joined}, limit),
        Cmp.is_lt(Encoding.cmp_low_zero(6n, low,
          Word.cmp(26n, high, Encoding.one(26n)))),
        cmp_lt, less_structural)
      less_high = Laws.low_zero_prefix_lt_implies_high_lt(
        6n, low,
        Word.cmp(26n, high, Encoding.one(26n)),
        less_low)
      high_zero = Laws.word_lt_one_is_zero(26n,
        high, less_high)
      clean = Equal.cong(Word(26n), U32,
        tail => U32{Encoding.append(26n, 6n, low, tail)},
        Word.zero(26n), high,
        Equal.sym(Word(26n), high, Word.zero(26n),
          high_zero))
      original = Equal.cong(Word(32n), U32,
        value => U32{value}, joined, word, join_eq)
      Equal.trans(U32,
        Encoding.square(low), U32{joined}, U32{word},
        clean, original)

def Laws.u32_under_64_is_canonical(x, less):
  match x:
    case U32{word}:
      canonical_under64_pair(word,
        Encoding.split(26n, 6n, word),
        Laws.word_append_split_inverse(6n, 26n, word),
        less)

def Laws.pawn_rank_after_single_push(pc, bound):
  +clean = Encoding.square(
    Encoding.low6(pc))
  +same = Laws.u32_under_64_is_canonical(
    pc, bound)
  Equal.trans(U32,
    Rules.rank(U32.add(pc, 8)),
    Rules.rank(U32.add(clean, 8)),
    U32.inc(Rules.rank(pc)),
    Equal.cong(U32, U32,
      value => Rules.rank(
        U32.add(value, 8)),
      pc, clean,
      Equal.sym(U32, clean, pc,
        same)),
    Equal.trans(U32,
      Rules.rank(U32.add(clean, 8)),
      U32.inc(Rules.rank(clean)),
      U32.inc(Rules.rank(pc)),
      PawnArithmetic.add8_rank(
        Encoding.low6(pc)),
      Equal.cong(U32, U32,
        value => U32.inc(
          Rules.rank(value)),
        clean, pc, same)))

def Laws.pawn_rank_after_double_push(pc, bound):
  +clean = Encoding.square(
    Encoding.low6(pc))
  +same = Laws.u32_under_64_is_canonical(
    pc, bound)
  Equal.trans(U32,
    Rules.rank(U32.add(pc, 16)),
    Rules.rank(U32.add(clean, 16)),
    U32.add(Rules.rank(pc), 2),
    Equal.cong(U32, U32,
      value => Rules.rank(
        U32.add(value, 16)),
      pc, clean,
      Equal.sym(U32, clean, pc,
        same)),
    Equal.trans(U32,
      Rules.rank(U32.add(clean, 16)),
      U32.add(Rules.rank(clean), 2),
      U32.add(Rules.rank(pc), 2),
      PawnArithmetic.add16_rank(
        Encoding.low6(pc)),
      Equal.cong(U32, U32,
        value => U32.add(
          Rules.rank(value), 2),
        clean, pc, same)))

def Laws.pawn_rank_below_max(pc, bound):
  +clean = Encoding.square(
    Encoding.low6(pc))
  +same = Laws.u32_under_64_is_canonical(
    pc, bound)
  +arithmetic =
    PawnArithmetic.rank_below_max(
      Encoding.low6(pc))
  clean_bound = equality_cast(Bool,
    Laws.Truth,
    True{}, U32.is_lt(
      Rules.rank(clean),
      4294967295),
    Equal.sym(Bool,
      U32.is_lt(Rules.rank(clean),
        4294967295),
      True{}, arithmetic),
    Unit{})
  equality_cast(U32,
    value => Laws.Truth(
      U32.is_lt(Rules.rank(value),
        4294967295)),
    clean, pc, same, clean_bound)

def pawn_nat_rank_shift_lift(
  +pc: U32, +offset: U32,
  +addition: Nat,
  bound: Laws.Truth(U32.is_lt(pc, 64)),
  clean_step:
    {U32.to_nat(Rules.rank(U32.add(
        Encoding.square(Encoding.low6(pc)),
        offset))) ==
      Nat.add(addition,
        U32.to_nat(Rules.rank(
          Encoding.square(
            Encoding.low6(pc))))) : Nat}) ->
  {U32.to_nat(Rules.rank(
      U32.add(pc, offset))) ==
    Nat.add(addition,
      U32.to_nat(Rules.rank(pc))) : Nat}:
  +clean = Encoding.square(
    Encoding.low6(pc))
  +same = Laws.u32_under_64_is_canonical(
    pc, bound)
  Equal.trans(Nat,
    U32.to_nat(Rules.rank(
      U32.add(pc, offset))),
    U32.to_nat(Rules.rank(
      U32.add(clean, offset))),
    Nat.add(addition,
      U32.to_nat(Rules.rank(pc))),
    Equal.cong(U32, Nat,
      value => U32.to_nat(Rules.rank(
        U32.add(value, offset))),
      pc, clean,
      Equal.sym(U32, clean, pc,
        same)),
    Equal.trans(Nat,
      U32.to_nat(Rules.rank(
        U32.add(clean, offset))),
      Nat.add(addition,
        U32.to_nat(Rules.rank(clean))),
      Nat.add(addition,
        U32.to_nat(Rules.rank(pc))),
      clean_step,
      Equal.cong(U32, Nat,
        value => Nat.add(addition,
          U32.to_nat(Rules.rank(
            value))),
        clean, pc, same)))

def Laws.pawn_nat_rank_after_single_push(
  pc, bound):
  pawn_nat_rank_shift_lift(pc,
    8, 1n, bound,
    PawnArithmetic.nat_rank_add8(
      Encoding.low6(pc)))

def Laws.pawn_nat_rank_after_double_push(
  pc, bound):
  pawn_nat_rank_shift_lift(pc,
    16, 2n, bound,
    PawnArithmetic.nat_rank_add16(
      Encoding.low6(pc)))

def Laws.pawn_rank_positive_nat(pc,
  bound, positive):
  +clean = Encoding.square(
    Encoding.low6(pc))
  +same = Laws.u32_under_64_is_canonical(
    pc, bound)
  bool_eq = Equal.trans(Bool,
    U32.is_gt(Rules.rank(pc), 0),
    U32.is_gt(Rules.rank(clean), 0),
    Nat.is_gt(U32.to_nat(
      Rules.rank(pc)), 0n),
    Equal.cong(U32, Bool,
      value => U32.is_gt(
        Rules.rank(value), 0),
      pc, clean,
      Equal.sym(U32, clean, pc,
        same)),
    Equal.trans(Bool,
      U32.is_gt(Rules.rank(clean), 0),
      Nat.is_gt(U32.to_nat(
        Rules.rank(clean)), 0n),
      Nat.is_gt(U32.to_nat(
        Rules.rank(pc)), 0n),
      PawnArithmetic.rank_positive_equiv(
        Encoding.low6(pc)),
      Equal.cong(U32, Bool,
        value => Nat.is_gt(
          U32.to_nat(Rules.rank(value)),
          0n), clean, pc, same)))
  equality_cast(Bool, Laws.Truth,
    U32.is_gt(Rules.rank(pc), 0),
    Nat.is_gt(U32.to_nat(
      Rules.rank(pc)), 0n),
    bool_eq, positive)

def Laws.pawn_rank_below_seven_nat(pc,
  bound, upper):
  +clean = Encoding.square(
    Encoding.low6(pc))
  +same = Laws.u32_under_64_is_canonical(
    pc, bound)
  bool_eq = Equal.trans(Bool,
    U32.is_lt(Rules.rank(pc), 7),
    U32.is_lt(Rules.rank(clean), 7),
    Nat.is_lt(U32.to_nat(
      Rules.rank(pc)), 7n),
    Equal.cong(U32, Bool,
      value => U32.is_lt(
        Rules.rank(value), 7),
      pc, clean,
      Equal.sym(U32, clean, pc,
        same)),
    Equal.trans(Bool,
      U32.is_lt(Rules.rank(clean), 7),
      Nat.is_lt(U32.to_nat(
        Rules.rank(clean)), 7n),
      Nat.is_lt(U32.to_nat(
        Rules.rank(pc)), 7n),
      PawnArithmetic.rank_below7_equiv(
        Encoding.low6(pc)),
      Equal.cong(U32, Bool,
        value => Nat.is_lt(
          U32.to_nat(Rules.rank(value)),
          7n), clean, pc, same)))
  equality_cast(Bool, Laws.Truth,
    U32.is_lt(Rules.rank(pc), 7),
    Nat.is_lt(U32.to_nat(
      Rules.rank(pc)), 7n),
    bool_eq, upper)

def Laws.pawn_valid_rank_bounds(wk, bk,
  pc, turn, valid):
  +placement = Rules.placement_valid(
    4, wk, bk, pc, turn)
  +kings = Bool.not(
    Position.kings_touch(wk, bk))
  +pawn = U32.is_gt(
    Rules.rank(pc), 0) &&
    U32.is_lt(Rules.rank(pc), 7)
  +check = U32.is_eq(turn, 1) ||
    Bool.not(Rules.attacks(4, pc,
      bk, wk))
  first = and_left(
    (placement && kings) && pawn,
    check, valid)
  second = and_right(placement && kings,
    pawn, first)
  truth_and_split(
    U32.is_gt(Rules.rank(pc), 0),
    U32.is_lt(Rules.rank(pc), 7),
    second)

def Laws.square_list_complete(x, less):
  +word = Encoding.low6(x)
  found = square_member_encode(word, Squares.words(6n),
    Laws.square_words_complete(6n, word))
  equality_cast(U32,
    value => Squares.Member(U32, value, Squares.all6()),
    Encoding.square(word), x,
    Laws.u32_under_64_is_canonical(x, less), found)

def Laws.retro_new_squares_complete():
  dest => less => Laws.square_list_complete(dest, less)

def canonical_under2_pair(+word: Word(32n),
  pair: Word(1n) & Word(31n),
  +join_eq: {Encoding.join(1n, 31n, pair) == word : Word(32n)},
  less: Laws.Truth(U32.is_lt(U32{word}, 2))) ->
  {Encoding.turn(WCon{Encoding.low1.fin(pair),
      Word.zero(13n)}) == U32{word} : U32}:
  match pair:
    case (low, +high):
      match low:
        case WCon{+bit, WNil{}}:
          +joined = Encoding.append(31n, 1n,
            WCon{bit, WNil{}}, high)
          +limit = {U32{Encoding.append(31n, 1n,
            Word.zero(1n), Encoding.one(31n))} : U32}
          word_to_joined = Equal.sym(Word(32n),
            joined, word, join_eq)
          lt_word_to_joined = Equal.cong(Word(32n), Bool,
            value => U32.is_lt(U32{value}, 2),
            word, joined, word_to_joined)
          less_joined = equality_cast(Bool, Laws.Truth,
            U32.is_lt(U32{word}, 2),
            U32.is_lt(U32{joined}, 2),
            lt_word_to_joined, less)
          lt_limit = Equal.cong(U32, Bool,
            value => U32.is_lt(U32{joined}, value),
            2, limit,
            Equal.sym(U32, limit, 2,
              Laws.structural_two_is_2()))
          less_structural = equality_cast(Bool, Laws.Truth,
            U32.is_lt(U32{joined}, 2),
            U32.is_lt(U32{joined}, limit),
            lt_limit, less_joined)
          cmp_eq = Laws.word_cmp_append_zero_prefix(
            1n, 31n, WCon{bit, WNil{}},
            high, Encoding.one(31n))
          cmp_lt = Equal.cong(Cmp, Bool,
            value => Cmp.is_lt(value),
            Word.cmp(32n, joined,
              Encoding.append(31n, 1n,
                Word.zero(1n), Encoding.one(31n))),
            Encoding.cmp_low_zero(1n,
              WCon{bit, WNil{}},
              Word.cmp(31n, high, Encoding.one(31n))),
            cmp_eq)
          less_low = equality_cast(Bool, Laws.Truth,
            U32.is_lt(U32{joined}, limit),
            Cmp.is_lt(Encoding.cmp_low_zero(1n,
              WCon{bit, WNil{}},
              Word.cmp(31n, high, Encoding.one(31n)))),
            cmp_lt, less_structural)
          less_high = Laws.low_zero_prefix_lt_implies_high_lt(
            1n, WCon{bit, WNil{}},
            Word.cmp(31n, high, Encoding.one(31n)),
            less_low)
          high_zero = Laws.word_lt_one_is_zero(31n,
            high, less_high)
          clean = Equal.cong(Word(31n), U32,
            tail => U32{WCon{bit, tail}},
            Word.zero(31n), high,
            Equal.sym(Word(31n), high, Word.zero(31n),
              high_zero))
          original = Equal.cong(Word(32n), U32,
            value => U32{value}, joined, word, join_eq)
          Equal.trans(U32,
            Encoding.turn(WCon{bit, Word.zero(13n)}),
            U32{joined}, U32{word}, clean, original)

def Laws.u32_under_2_is_canonical_turn(x, less):
  match x:
    case U32{word}:
      first = Equal.cong(Bool, U32,
        bit => Encoding.turn(WCon{bit, Word.zero(13n)}),
        Encoding.low1(U32{word}),
        Encoding.low1.fin(Encoding.split(31n, 1n, word)),
        Laws.low_one_bit_matches_split(word))
      second = canonical_under2_pair(word,
        Encoding.split(31n, 1n, word),
        Laws.word_append_split_inverse(1n, 31n, word),
        less)
      Equal.trans(U32,
        Encoding.turn(WCon{Encoding.low1(U32{word}),
          Word.zero(13n)}),
        Encoding.turn(WCon{
          Encoding.low1.fin(Encoding.split(31n, 1n, word)),
          Word.zero(13n)}),
        U32{word}, first, second)

def Laws.valid_implies_placement(kind, wk, bk, pc,
  side, valid):
  +placement = Rules.placement_valid(kind, wk, bk, pc, side)
  +kings = Bool.not(Position.kings_touch(wk, bk))
  +pawn = Bool.not(U32.is_eq(kind, 4)) ||
    (U32.is_gt(Rules.rank(pc), 0) &&
      U32.is_lt(Rules.rank(pc), 7))
  +check = U32.is_eq(side, 1) ||
    Bool.not(Rules.attacks(kind, pc, bk, wk))
  first = and_left((placement && kings) && pawn,
    check, valid)
  second = and_left(placement && kings, pawn, first)
  and_left(placement, kings, second)

def Laws.placement_implies_ranges(kind, wk, bk, pc,
  side, placement):
  +a = U32.is_lt(kind, 5)
  +b = U32.is_lt(side, 2)
  +c = U32.is_lt(wk, 64)
  +d = U32.is_lt(bk, 64)
  +e = U32.is_lt(pc, 64)
  +f = U32.is_ne(wk, bk)
  +g = U32.is_ne(wk, pc)
  +h = U32.is_ne(bk, pc)
  +p2 = a && b
  +p3 = p2 && c
  +p4 = p3 && d
  +p5 = p4 && e
  +p6 = p5 && f
  +p7 = p6 && g
  q7 = and_left(p7, h, placement)
  q6 = and_left(p6, g, q7)
  +q5 = and_left(p5, f, q6)
  +q4 = and_left(p4, e, q5)
  +q3 = and_left(p3, d, q4)
  +q2 = and_left(p2, c, q3)
  side_range = and_right(a, b, q2)
  wk_range = and_right(p2, c, q3)
  bk_range = and_right(p3, d, q4)
  pc_range = and_right(p4, e, q5)
  (side_range, wk_range, bk_range, pc_range)

def valid_roundtrip_from_ranges(+wk: U32, +bk: U32,
  +pc: U32, +side: U32,
  ranges: Laws.Truth(U32.is_lt(side, 2)) &
    Laws.Truth(U32.is_lt(wk, 64)) &
    Laws.Truth(U32.is_lt(bk, 64)) &
    Laws.Truth(U32.is_lt(pc, 64))) ->
  {Rules.decode(Rules.index(
      Rules.State{wk, bk, pc, side})) ==
    Rules.State{wk, bk, pc, side} : Rules.State}:
  match ranges:
    case (side_range, wk_range, bk_range, pc_range):
      +a = Encoding.square(Encoding.low6(wk))
      +b = Encoding.square(Encoding.low6(bk))
      +c = Encoding.square(Encoding.low6(pc))
      +d = Encoding.turn(WCon{Encoding.low1(side),
        Word.zero(13n)})
      start = Laws.executable_decode_index_is_canonical(
        wk, bk, pc, side)
      first = Equal.cong(U32, Rules.State,
        value => Rules.State{value, b, c, d},
        a, wk, Laws.u32_under_64_is_canonical(wk, wk_range))
      second = Equal.cong(U32, Rules.State,
        value => Rules.State{wk, value, c, d},
        b, bk, Laws.u32_under_64_is_canonical(bk, bk_range))
      third = Equal.cong(U32, Rules.State,
        value => Rules.State{wk, bk, value, d},
        c, pc, Laws.u32_under_64_is_canonical(pc, pc_range))
      fourth = Equal.cong(U32, Rules.State,
        value => Rules.State{wk, bk, pc, value},
        d, side,
        Laws.u32_under_2_is_canonical_turn(side, side_range))
      step1 = Equal.trans(Rules.State,
        Rules.decode(Rules.index(
          Rules.State{wk, bk, pc, side})),
        Rules.State{a, b, c, d},
        Rules.State{wk, b, c, d},
        start, first)
      step2 = Equal.trans(Rules.State,
        Rules.decode(Rules.index(
          Rules.State{wk, bk, pc, side})),
        Rules.State{wk, b, c, d},
        Rules.State{wk, bk, c, d},
        step1, second)
      step3 = Equal.trans(Rules.State,
        Rules.decode(Rules.index(
          Rules.State{wk, bk, pc, side})),
        Rules.State{wk, bk, c, d},
        Rules.State{wk, bk, pc, d},
        step2, third)
      Equal.trans(Rules.State,
        Rules.decode(Rules.index(
          Rules.State{wk, bk, pc, side})),
        Rules.State{wk, bk, pc, d},
        Rules.State{wk, bk, pc, side},
        step3, fourth)

def Laws.valid_state_index_roundtrip(kind, wk, bk, pc,
  side, valid):
  placement = Laws.valid_implies_placement(
    kind, wk, bk, pc, side, valid)
  valid_roundtrip_from_ranges(wk, bk, pc, side,
    Laws.placement_implies_ranges(
      kind, wk, bk, pc, side, placement))

def truncate19_fin_as_clocked_low(
  pair: Word(19n) & Word(13n)) ->
  {Encoding.truncate19.fin(pair) ==
    U32{Encoding.append(13n, 19n,
      ClockedIndex.low19.fin(pair),
      Word.zero(13n))} : U32}:
  match pair:
    case (low, high):
      {==}

def Laws.truncate19_is_explicit_low_word(index):
  match index:
    case U32{word}:
      truncate19_fin_as_clocked_low(
        Encoding.split(13n, 19n, word))

def Laws.valid_state_index_is_canonical_low_word(
  kind, wk, bk, pc, side, valid):
  +state = {Rules.State{wk, bk, pc, side} :
    Rules.State}
  +index = Rules.index(state)
  +masked = U32.and(index, 524287)
  +truncated = Encoding.truncate19(index)
  +explicit = {U32{Encoding.append(13n,
    19n, ClockedIndex.low19(index),
    Word.zero(13n))} : U32}
  roundtrip = Laws.valid_state_index_roundtrip(
    kind, wk, bk, pc, side, valid)
  repack = Equal.sym(U32,
    Rules.index(Rules.decode(index)),
    index,
    Equal.cong(Rules.State, U32,
      value => Rules.index(value),
      Rules.decode(index), state,
      roundtrip))
  Equal.trans(U32, index,
    Rules.index(Rules.decode(index)),
    explicit, repack,
    Equal.trans(U32,
      Rules.index(Rules.decode(index)),
      masked, explicit,
      Laws.executable_repack_is_nineteen_bit_mask(
        index),
      Equal.trans(U32, masked,
        truncated, explicit,
        Laws.fast_nineteen_bit_mask_matches_truncation(
          index),
        Laws.truncate19_is_explicit_low_word(
          index))))

def Laws.u32_equality_reflects_identity(x, y, equal):
  match x y:
    case U32{+a} U32{+b}:
      bits = word_cmp_equality_reflect(32n, a, b, equal)
      Equal.cong(Word(32n), U32, w => U32{w}, a, b, bits)

def Laws.square_list_equals_refl(squares):
  match squares:
    case Nil{}:
      Unit{}
    case head <> tail:
      and_intro(U32.is_eq(head,
          head),
        Squares.equals(tail, tail),
        Laws.u32_equality_reflexive(
          head),
        Laws.square_list_equals_refl(
          tail))

def Laws.square_list_equals_member_transfer(
  xs, ys, value, same, member):
  match xs ys member:
    case Nil{} Nil{} impossible:
      match impossible:
    case Nil{} y <> tail Inl{head}:
      Empty.absurd(
        Squares.Member(U32, value,
          Nil{}), same)
    case Nil{} y <> tail Inr{later}:
      Empty.absurd(
        Squares.Member(U32, value,
          Nil{}), same)
    case x <> rest Nil{} impossible:
      match impossible:
    case x <> rest y <> tail
         Inl{head}:
      +equal_head = and_left(
        U32.is_eq(x, y),
        Squares.equals(rest,
          tail), same)
      Inl{Equal.trans(U32,
        value, y, x, head,
        Equal.sym(U32, x, y,
          Laws.u32_equality_reflects_identity(
            x, y, equal_head)))}
    case x <> rest y <> tail
         Inr{later}:
      Inr{Laws.square_list_equals_member_transfer(
        rest, tail, value,
        and_right(U32.is_eq(x, y),
          Squares.equals(rest,
            tail), same),
        later)}

def Laws.nat_equality_reflects_identity(
  a, b, equal):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+rest:
      match equal:
    case 1n+rest 0n:
      match equal:
    case 1n+rest 1n+tail:
      Equal.cong(Nat, Nat,
        value => 1n+value,
        rest, tail,
        Laws.nat_equality_reflects_identity(
          rest, tail, equal))

def laws_truth_to_wdl_truth(+b: Bool,
  proof: Laws.Truth(b)) -> WDL.Truth(b):
  match b:
    case True{}:
      Unit{}
    case False{}:
      Empty.absurd(Laws.Truth(b), proof)

def wdl_truth_to_laws_truth(+b: Bool,
  proof: WDL.Truth(b)) -> Laws.Truth(b):
  match b:
    case True{}:
      Unit{}
    case False{}:
      proof

def or_left(+a: Bool, b: Bool,
  proof: Laws.Truth(a)) -> Laws.Truth(a || b):
  match a:
    case True{}:
      Unit{}
    case False{}:
      Empty.absurd(Laws.Truth(b), proof)

def or_right(+a: Bool, b: Bool,
  proof: Laws.Truth(b)) -> Laws.Truth(a || b):
  match a:
    case True{}:
      Unit{}
    case False{}:
      proof

def Laws.same_class_white_move_is_a_game_move(kind, wk, bk, pc,
  wk2, bk2, pc2, legal):
  same = Laws.u32_equality_reflexive(kind)
  first = and_intro(U32.is_eq(kind, kind),
    Rules.move_to(kind, Rules.State{wk, bk, pc, 0},
      Rules.State{wk2, bk2, pc2, 1}), same, legal)
  win_move = or_left(U32.is_eq(kind, kind) &&
    Rules.move_to(kind, Rules.State{wk, bk, pc, 0},
      Rules.State{wk2, bk2, pc2, 1}),
    U32.is_eq(kind, 4) && U32.is_lt(kind, 2) &&
      WDL.promotion(wk, bk, pc, kind, wk2, bk2, pc2), first)
  laws_truth_to_wdl_truth(WDL.move(
    WDL.White{kind, wk, bk, pc},
    WDL.Black{kind, wk2, bk2, pc2}), win_move)

def Laws.same_class_black_move_is_a_game_move(kind, wk, bk, pc,
  wk2, bk2, pc2, legal):
  same = Laws.u32_equality_reflexive(kind)
  first = and_intro(U32.is_eq(kind, kind),
    Rules.move_to(kind, Rules.State{wk, bk, pc, 1},
      Rules.State{wk2, bk2, pc2, 0}), same, legal)
  laws_truth_to_wdl_truth(WDL.move(
    WDL.Black{kind, wk, bk, pc},
    WDL.White{kind, wk2, bk2, pc2}), first)

def or_cases(-R: Type, +a: Bool, +b: Bool,
  proof: Laws.Truth(a || b),
  left: Laws.Truth(a) -> R,
  right: Laws.Truth(b) -> R) -> R:
  match a:
    case True{}:
      left(Unit{})
    case False{}:
      right(proof)

def pawn_piece_step_is_forward(
  +pc: U32, +dest: U32,
  +wk: U32, +bk: U32) ->
  {Rules.piece_step(4, pc, dest,
      wk, bk) ==
    (U32.is_ne(pc, dest) &&
      Rules.pawn_step(pc, dest,
        wk, bk)) : Bool}:
  +forward = Rules.pawn_step(pc,
    dest, wk, bk)
  +change = U32.is_ne(pc, dest)
  Equal.trans(Bool,
    Rules.piece_step(4, pc,
      dest, wk, bk),
    change && (forward || False{}),
    change && forward,
    Equal.cong(Bool, Bool,
      option => change && option,
      (forward || False{}) ||
        False{},
      forward || False{},
      bool_or_false_right(
        forward || False{})),
    Equal.cong(Bool, Bool,
      option => change && option,
      forward || False{},
      forward,
      bool_or_false_right(forward)))

def Laws.legal_pawn_piece_move_is_push(
  wk, bk, pc, dest, legal,
  changed):
  +from = {Rules.State{wk, bk,
    pc, 0} : Rules.State}
  +target = {Rules.State{wk, bk,
    dest, 1} : Rules.State}
  +valid_from = Rules.valid(4, from)
  +valid_to = Rules.valid(4, target)
  +same_bk = U32.is_eq(bk, bk)
  +king = U32.is_eq(pc, dest) &&
    Rules.king_step(wk, wk)
  +piece = U32.is_eq(wk, wk) &&
    Rules.piece_step(4, pc, dest,
      wk, bk)
  choice = and_right(
    valid_from && valid_to &&
      same_bk,
    king || piece, legal)
  or_cases(Laws.Truth(Rules.pawn_step(
      pc, dest, wk, bk)),
    king, piece, choice,
    king_yes =>
      Empty.absurd(
        Laws.Truth(Rules.pawn_step(
          pc, dest, wk, bk)),
        true_and_not_absurd(
          U32.is_eq(pc, dest),
          and_left(U32.is_eq(pc,
            dest),
            Rules.king_step(wk, wk),
            king_yes),
          changed)),
    piece_yes =>
      and_right(U32.is_ne(pc, dest),
        Rules.pawn_step(pc, dest,
          wk, bk),
        equality_cast(Bool,
          Laws.Truth,
          Rules.piece_step(4, pc,
            dest, wk, bk),
          U32.is_ne(pc, dest) &&
            Rules.pawn_step(pc, dest,
              wk, bk),
          pawn_piece_step_is_forward(
            pc, dest, wk, bk),
          and_right(U32.is_eq(wk,
            wk),
            Rules.piece_step(4, pc,
              dest, wk, bk),
            piece_yes))))

def Laws.game_move_with_same_white_material_is_a_rules_move(kind,
  wk, bk, pc, wk2, bk2, pc2, move):
  +same = U32.is_eq(kind, kind)
  +edge = Rules.move_to(kind, Rules.State{wk, bk, pc, 0},
    Rules.State{wk2, bk2, pc2, 1})
  +pawn = U32.is_eq(kind, 4)
  +small = U32.is_lt(kind, 2)
  promoted = WDL.promotion(wk, bk, pc, kind, wk2, bk2, pc2)
  or_cases(Laws.Truth(edge), same && edge,
    pawn && small && promoted,
    wdl_truth_to_laws_truth(WDL.move(
      WDL.White{kind, wk, bk, pc},
      WDL.Black{kind, wk2, bk2, pc2}), move),
    ordinary => and_right(same, edge, ordinary),
    impossible =>
      +first = and_left(pawn && small, promoted, impossible)
      equal = and_left(pawn, small, first)
      less = and_right(pawn, small, first)
      identity = Laws.u32_equality_reflects_identity(kind, 4, equal)
      absurd = equality_cast(U32,
        k => Laws.Truth(U32.is_lt(k, 2)),
        kind, 4, identity, less)
      Empty.absurd(Laws.Truth(edge), absurd))

def Laws.game_move_with_same_black_material_is_a_rules_move(kind,
  wk, bk, pc, wk2, bk2, pc2, move):
  and_right(U32.is_eq(kind, kind),
    Rules.move_to(kind, Rules.State{wk, bk, pc, 1},
      Rules.State{wk2, bk2, pc2, 0}),
    wdl_truth_to_laws_truth(WDL.move(
      WDL.Black{kind, wk, bk, pc},
      WDL.White{kind, wk2, bk2, pc2}), move))

def Laws.legal_black_capture_is_a_draw_exit(kind, wk, bk, pc,
  valid, capture):
  combined = and_intro(
    Rules.valid(kind, Rules.State{wk, bk, pc, 1}),
    Rules.black_move(kind, wk, bk, pc, pc), valid, capture)
  laws_truth_to_wdl_truth(WDL.move(
    WDL.Black{kind, wk, bk, pc}, WDL.KingsOnly{}), combined)

def Laws.game_draw_exit_is_a_legal_black_capture(kind, wk, bk,
  pc, move):
  +combined = wdl_truth_to_laws_truth(WDL.move(
    WDL.Black{kind, wk, bk, pc}, WDL.KingsOnly{}), move)
  valid = and_left(
    Rules.valid(kind, Rules.State{wk, bk, pc, 1}),
    Rules.black_move(kind, wk, bk, pc, pc), combined)
  capture = and_right(
    Rules.valid(kind, Rules.State{wk, bk, pc, 1}),
    Rules.black_move(kind, wk, bk, pc, pc), combined)
  (valid, capture)

def Laws.semantic_promotion_has_seed_shape(wk, bk, pc,
  kind, wk2, bk2, pc2, promotion):
  and_left(Rules.pawn_can_promote(wk, bk, pc),
    U32.is_lt(kind, 4) &&
      U32.is_eq(wk, wk2) && U32.is_eq(bk, bk2) &&
      U32.is_eq(pc2, (pc + 8 : U32)) &&
      Rules.valid(kind, Rules.State{wk2, bk2, pc2, 1}),
    wdl_truth_to_laws_truth(WDL.promotion(wk, bk, pc,
      kind, wk2, bk2, pc2), promotion))

def Laws.legal_pawn_seed_has_semantic_promotion(wk, bk, pc,
  kind, can, bound, target_valid):
  +target = (pc + 8 : U32)
  same_wk = Laws.u32_equality_reflexive(wk)
  same_bk = Laws.u32_equality_reflexive(bk)
  same_pc = Laws.u32_equality_reflexive(target)
  step1 = and_intro(U32.is_lt(kind, 4),
    U32.is_eq(wk, wk), bound, same_wk)
  step2 = and_intro(U32.is_lt(kind, 4) && U32.is_eq(wk, wk),
    U32.is_eq(bk, bk), step1, same_bk)
  step3 = and_intro(
    U32.is_lt(kind, 4) && U32.is_eq(wk, wk) &&
      U32.is_eq(bk, bk),
    U32.is_eq(target, target), step2, same_pc)
  step4 = and_intro(
    U32.is_lt(kind, 4) && U32.is_eq(wk, wk) &&
      U32.is_eq(bk, bk) && U32.is_eq(target, target),
    Rules.valid(kind, Rules.State{wk, bk, target, 1}),
    step3, target_valid)
  full = and_intro(Rules.pawn_can_promote(wk, bk, pc),
    U32.is_lt(kind, 4) && U32.is_eq(wk, wk) &&
      U32.is_eq(bk, bk) && U32.is_eq(target, target) &&
      Rules.valid(kind, Rules.State{wk, bk, target, 1}),
    can, step4)
  laws_truth_to_wdl_truth(WDL.promotion(wk, bk, pc,
    kind, wk, bk, target), full)

def Laws.pawn_queen_or_rook_promotion_is_game_move(wk, bk, pc,
  kind, wk2, bk2, pc2, bound, promotion):
  first = and_intro(U32.is_eq(4, 4), U32.is_lt(kind, 2),
    Laws.u32_equality_reflexive(4), bound)
  right = and_intro(U32.is_eq(4, 4) && U32.is_lt(kind, 2),
    WDL.promotion(wk, bk, pc, kind, wk2, bk2, pc2),
    first, wdl_truth_to_laws_truth(
      WDL.promotion(wk, bk, pc, kind, wk2, bk2, pc2),
      promotion))
  combined = or_right(U32.is_eq(4, kind) &&
    Rules.move_to(4, Rules.State{wk, bk, pc, 0},
      Rules.State{wk2, bk2, pc2, 1}),
    U32.is_eq(4, 4) && U32.is_lt(kind, 2) &&
      WDL.promotion(wk, bk, pc, kind, wk2, bk2, pc2),
    right)
  laws_truth_to_wdl_truth(WDL.move(
    WDL.White{4, wk, bk, pc},
    WDL.Black{kind, wk2, bk2, pc2}), combined)

def Laws.game_move_to_queen_or_rook_is_promotion(wk, bk, pc,
  kind, wk2, bk2, pc2, bound, move):
  +promotion = WDL.promotion(wk, bk, pc,
    kind, wk2, bk2, pc2)
  +first = U32.is_eq(4, kind) &&
    Rules.move_to(4, Rules.State{wk, bk, pc, 0},
      Rules.State{wk2, bk2, pc2, 1})
  +second = U32.is_eq(4, 4) && U32.is_lt(kind, 2) &&
    promotion
  or_cases(WDL.Truth(promotion), first, second,
    wdl_truth_to_laws_truth(WDL.move(
      WDL.White{4, wk, bk, pc},
      WDL.Black{kind, wk2, bk2, pc2}), move),
    ordinary =>
      equal = and_left(U32.is_eq(4, kind),
        Rules.move_to(4, Rules.State{wk, bk, pc, 0},
          Rules.State{wk2, bk2, pc2, 1}), ordinary)
      identity = Laws.u32_equality_reflects_identity(
        4, kind, equal)
      impossible = equality_cast(U32,
        k => Laws.Truth(U32.is_lt(k, 2)),
        kind, 4, Equal.sym(U32, 4, kind, identity),
        bound)
      Empty.absurd(WDL.Truth(promotion), impossible),
    promoted =>
      laws_truth_to_wdl_truth(promotion,
        and_right(U32.is_eq(4, 4) && U32.is_lt(kind, 2),
          promotion, promoted)))

def Laws.bishop_promotion_is_draw_exit(wk, bk, pc,
  promotion):
  +target = (pc + 8 : U32)
  combined = and_intro(U32.is_eq(4, 4),
    WDL.promotion(wk, bk, pc, 2, wk, bk, target),
    Laws.u32_equality_reflexive(4),
    wdl_truth_to_laws_truth(WDL.promotion(wk, bk, pc,
      2, wk, bk, target), promotion))
  laws_truth_to_wdl_truth(WDL.move(
    WDL.White{4, wk, bk, pc}, WDL.BareBishop{}),
    combined)

def Laws.knight_promotion_is_draw_exit(wk, bk, pc,
  promotion):
  +target = (pc + 8 : U32)
  combined = and_intro(U32.is_eq(4, 4),
    WDL.promotion(wk, bk, pc, 3, wk, bk, target),
    Laws.u32_equality_reflexive(4),
    wdl_truth_to_laws_truth(WDL.promotion(wk, bk, pc,
      3, wk, bk, target), promotion))
  laws_truth_to_wdl_truth(WDL.move(
    WDL.White{4, wk, bk, pc}, WDL.BareKnight{}),
    combined)

def equal_and_unequal_absurd(+cmp: Cmp,
  equal: Laws.Truth(Cmp.is_eq(cmp)),
  unequal: Laws.Truth(Bool.not(Cmp.is_eq(cmp)))) -> Empty:
  match cmp:
    case LT{}:
      equal
    case EQ{}:
      unequal
    case GT{}:
      equal

def either_step_is_nontrivial(+a: Bool, +b: Bool,
  disjunct: Laws.Truth(a || b),
  left: Laws.Truth(a) -> Empty,
  right: Laws.Truth(b) -> Empty) -> Empty:
  match a:
    case True{}:
      left(Unit{})
    case False{}:
      right(disjunct)

def white_king_step_contradiction(+wk: U32, +wk2: U32,
  same: Laws.Truth(U32.is_eq(wk, wk2)),
  legal: Laws.Truth(Rules.king_step(wk, wk2))) -> Empty:
  different = and_left(U32.is_ne(wk, wk2),
    Position.kings_touch(wk, wk2), legal)
  equal_and_unequal_absurd(U32.cmp(wk, wk2), same, different)

def white_piece_step_contradiction(+kind: U32, +pc: U32,
  +pc2: U32, +wk: U32, +bk: U32,
  same: Laws.Truth(U32.is_eq(pc, pc2)),
  legal: Laws.Truth(Rules.piece_step(kind, pc, pc2, wk, bk))) ->
  Empty:
  different = and_left(U32.is_ne(pc, pc2),
    (U32.is_eq(kind, 4) && Rules.pawn_step(pc, pc2, wk, bk)) ||
    (U32.is_eq(kind, 3) && Rules.knight_jump(pc, pc2)) ||
    (Rules.line_attack(kind, pc, pc2) &&
      Bool.not(Rules.on_segment(pc, pc2, wk)) &&
      Bool.not(Rules.on_segment(pc, pc2, bk))), legal)
  equal_and_unequal_absurd(U32.cmp(pc, pc2), same, different)

def Laws.white_same_class_move_changes_king_or_piece(kind, wk, bk,
  pc, wk2, bk2, pc2, legal, same_king, same_piece):
  valid_from = Rules.valid(kind, Rules.State{wk, bk, pc, 0})
  valid_to = Rules.valid(kind, Rules.State{wk2, bk2, pc2, 1})
  same_bk = U32.is_eq(bk, bk2)
  +same_pc = U32.is_eq(pc, pc2)
  +step_wk = Rules.king_step(wk, wk2)
  +same_wk = U32.is_eq(wk, wk2)
  +step_pc = Rules.piece_step(kind, pc, pc2, wk, bk)
  choices = and_right(valid_from && valid_to && same_bk,
    (same_pc && step_wk) || (same_wk && step_pc), legal)
  either_step_is_nontrivial(same_pc && step_wk,
    same_wk && step_pc, choices,
    king_move => white_king_step_contradiction(wk, wk2,
      same_king, and_right(same_pc, step_wk, king_move)),
    piece_move => white_piece_step_contradiction(kind, pc,
      pc2, wk, bk, same_piece,
      and_right(same_wk, step_pc, piece_move)))

def Laws.black_king_stays_separated(kind, wk, bk, pc, dest, legal):
  +step = Rules.king_step(bk, dest)
  +separated = Bool.not(Position.kings_touch(wk, dest))
  capture_or_valid = U32.is_eq(dest, pc) ||
    Rules.valid(kind, Rules.State{wk, dest, pc, 0})
  first = and_left(step && separated, capture_or_valid, legal)
  and_right(step, separated, first)

def and_middle_false(+a: Bool, b: Bool,
  proof: Laws.Truth((a && False{}) && b)) -> Empty:
  first = and_left(a && False{}, b, proof)
  and_right(a, False{}, first)

def white_reverse_shape(valid_from: Bool, valid_to: Bool,
  same_bk: Bool, same_pc: Bool, king_step: Bool,
  same_wk: Bool, piece_step: Bool,
  legal: Laws.Truth(valid_from && valid_to && same_bk &&
    ((same_pc && king_step) || (same_wk && piece_step)))) ->
  Laws.Truth(same_bk && (same_pc || same_wk)):
  match same_bk same_pc same_wk:
    case False{} _ _:
      and_middle_false(valid_from && valid_to,
        (same_pc && king_step) || (same_wk && piece_step), legal)
    case True{} True{} _:
      Unit{}
    case True{} False{} True{}:
      Unit{}
    case True{} False{} False{}:
      and_right(valid_from && valid_to && True{}, False{}, legal)

def black_reverse_shape(+valid_from: Bool, +valid_to: Bool,
  same_wk: Bool, same_pc: Bool, king_step: Bool,
  legal: Laws.Truth(valid_from && valid_to && same_wk &&
    same_pc && king_step)) ->
  Laws.Truth(same_wk && same_pc):
  match same_wk same_pc:
    case False{} False{}:
      first = and_left(valid_from && valid_to && False{} && False{},
        king_step, legal)
      and_middle_false(valid_from && valid_to, False{}, first)
    case False{} True{}:
      first = and_left(valid_from && valid_to && False{} && True{},
        king_step, legal)
      and_middle_false(valid_from && valid_to, True{}, first)
    case True{} False{}:
      first = and_left(valid_from && valid_to && True{} && False{},
        king_step, legal)
      and_right(valid_from && valid_to && True{}, False{}, first)
    case True{} True{}:
      Unit{}

def Laws.every_white_move_has_reverse_search_shape(kind,
  wk, bk, pc, wk2, bk2, pc2, legal):
  white_reverse_shape(
    Rules.valid(kind, Rules.State{wk, bk, pc, 0}),
    Rules.valid(kind, Rules.State{wk2, bk2, pc2, 1}),
    U32.is_eq(bk, bk2), U32.is_eq(pc, pc2),
    Rules.king_step(wk, wk2), U32.is_eq(wk, wk2),
    Rules.piece_step(kind, pc, pc2, wk, bk), legal)

def Laws.every_black_move_has_reverse_search_shape(kind,
  wk, bk, pc, wk2, bk2, pc2, legal):
  black_reverse_shape(
    Rules.valid(kind, Rules.State{wk, bk, pc, 1}),
    Rules.valid(kind, Rules.State{wk2, bk2, pc2, 0}),
    U32.is_eq(wk, wk2), U32.is_eq(pc, pc2),
    Rules.king_step(bk, bk2), legal)

def middle_of_four(+a: Bool, +b: Bool, +c: Bool, d: Bool,
  proof: Laws.Truth(a && b && c && d)) -> Laws.Truth(b):
  first = and_left(a && b && c, d, proof)
  second = and_left(a && b, c, first)
  and_right(a, b, second)

def Laws.legal_three_man_position_has_no_black_king_check(kind,
  wk, bk, pc, turn, valid):
  middle_of_four(
    Rules.placement_valid(kind, wk, bk, pc, turn),
    Bool.not(Position.kings_touch(wk, bk)),
    Bool.not(U32.is_eq(kind, 4)) ||
      (U32.is_gt(Rules.rank(pc), 0) &&
        U32.is_lt(Rules.rank(pc), 7)),
    U32.is_eq(turn, 1) ||
      Bool.not(Rules.attacks(kind, pc, bk, wk)),
      valid)

def Laws.proof_tree_read_after_write(n, tree, bits, value):
  match n tree bits:
    case 0n ProofTree.Leaf{old} WNil{}:
      {==}
    case 1n+rest ProofTree.Leaf{old} WCon{bit, tail}:
      {==}
    case 0n ProofTree.Node{left, right} WNil{}:
      %Laws.proof_tree_read_after_write(0n, left,
        WNil{}, value) :
        {ProofTree.get(0n,
          ProofTree.set(0n, left, WNil{}, value),
          WNil{}) == _ : U32}
      {==}
    case 1n+rest ProofTree.Node{left, right} WCon{False{}, tail}:
      %Laws.proof_tree_read_after_write(rest, left,
        tail, value) :
        {ProofTree.get(rest, ProofTree.set(rest, left,
          tail, value), tail) == _ : U32}
      {==}
    case 1n+rest ProofTree.Node{left, right} WCon{True{}, tail}:
      %Laws.proof_tree_read_after_write(rest, right,
        tail, value) :
        {ProofTree.get(rest, ProofTree.set(rest, right,
          tail, value), tail) == _ : U32}
      {==}

def Laws.proof_tree_filled_get(n, value, bits):
  match n bits:
    case 0n WNil{}:
      {==}
    case 1n+rest WCon{False{}, tail}:
      %Laws.proof_tree_filled_get(rest, value, tail) :
        {ProofTree.get(rest,
          ProofTree.filled(rest, value), tail) == _ : U32}
      {==}
    case 1n+rest WCon{True{}, tail}:
      %Laws.proof_tree_filled_get(rest, value, tail) :
        {ProofTree.get(rest,
          ProofTree.filled(rest, value), tail) == _ : U32}
      {==}

def Laws.proof_tree_filled_is_full(n, value):
  match n:
    case 0n:
      Unit{}
    case 1n++rest:
      (Laws.proof_tree_filled_is_full(rest, value),
       Laws.proof_tree_filled_is_full(rest, value))

def Laws.uniform_tree_serialized_byte_zero(
  n, bits):
  +tree = ProofTree.filled(n, 0)
  Equal.trans(Maybe<&2, U32>,
    List.get(&2, U32,
      ProofTree.bytes(tree),
      ProofTree.byte_offset(
        n, bits)),
    Some{ProofTree.get(n,
      tree, bits)},
    Some{0},
    Laws.proof_tree_byte_at_path(
      n, tree,
      Laws.proof_tree_filled_is_full(
        n, 0), bits),
    Equal.cong(U32,
      Maybe<&2, U32>,
      value => Some{value},
      ProofTree.get(n,
        tree, bits), 0,
      Laws.proof_tree_filled_get(
        n, 0, bits)))

def Laws.proof_tree_set_preserves_full(n, tree, bits, value,
  full):
  match n tree bits:
    case 0n ProofTree.Leaf{old} WNil{}:
      Unit{}
    case 0n ProofTree.Node{left, right} WNil{}:
      match full:
    case 1n+rest ProofTree.Leaf{old} WCon{bit, tail}:
      match full:
    case 1n+rest ProofTree.Node{left, right}
         WCon{False{}, tail}:
      match full:
        case (left_full, right_full):
          (Laws.proof_tree_set_preserves_full(rest,
             left, tail, value, left_full), right_full)
    case 1n+rest ProofTree.Node{left, right}
         WCon{True{}, tail}:
      match full:
        case (left_full, right_full):
          (left_full,
           Laws.proof_tree_set_preserves_full(rest,
             right, tail, value, right_full))

def same_bit_tail_different(n: Nat, +bit: Bool,
  +a: Word(n), +b: Word(n),
  different: {WCon{bit, a} != WCon{bit, b} : Word(1n+n)}) ->
  {a != b : Word(n)}:
  equality => different(Equal.cong(Word(n), Word(1n+n),
    tail => WCon{bit, tail}, a, b, equality))

def Laws.proof_tree_write_preserves_other(n, tree,
  write_bits, read_bits, value, full, different):
  match n tree write_bits read_bits:
    case 0n any WNil{} WNil{}:
      Empty.absurd(
        {ProofTree.get(0n,
          ProofTree.set(0n, any, WNil{}, value), WNil{}) ==
          ProofTree.get(0n, any, WNil{}) : U32},
        different({==}))
    case 1n++rest ProofTree.Leaf{old}
         WCon{False{}, +a} WCon{False{}, +b}:
      match full:
    case 1n++rest ProofTree.Leaf{old}
         WCon{True{}, +a} WCon{True{}, +b}:
      match full:
    case 1n++rest ProofTree.Leaf{old}
         WCon{False{}, +a} WCon{True{}, +b}:
      match full:
    case 1n++rest ProofTree.Leaf{old}
         WCon{True{}, +a} WCon{False{}, +b}:
      match full:
    case 1n++rest ProofTree.Node{+left, +right}
         WCon{False{}, +a} WCon{False{}, +b}:
      match full:
        case (left_full, right_full):
          %Laws.proof_tree_write_preserves_other(rest,
            left, a, b, value, left_full,
            same_bit_tail_different(rest, False{},
              a, b, different)) :
            {ProofTree.get(rest,
              ProofTree.set(rest, left, a, value), b) ==
              _ : U32}
          {==}
    case 1n++rest ProofTree.Node{+left, +right}
         WCon{True{}, +a} WCon{True{}, +b}:
      match full:
        case (left_full, right_full):
          %Laws.proof_tree_write_preserves_other(rest,
            right, a, b, value, right_full,
            same_bit_tail_different(rest, True{},
              a, b, different)) :
            {ProofTree.get(rest,
              ProofTree.set(rest, right, a, value), b) ==
              _ : U32}
          {==}
    case 1n++rest ProofTree.Node{+left, +right}
         WCon{False{}, +a} WCon{True{}, +b}:
      {==}
    case 1n++rest ProofTree.Node{+left, +right}
         WCon{True{}, +a} WCon{False{}, +b}:
      {==}

def Laws.proof_tree_index_read_after_write(tree, index, value):
  Laws.proof_tree_read_after_write(19n, tree,
    ProofTree.bits19(index), value)

def tree_to_array_bytes_go(+tree: ProofTree.Tree,
  +acc: List<&2, U32>) ->
  {Output.bytes.go(ProofTree.to_array(tree), acc) ==
    ProofTree.bytes.go(tree, acc) : List<&2, U32>}:
  match tree:
    case ProofTree.Leaf{value}:
      {==}
    case ProofTree.Node{+left, +right}:
      right_proof = tree_to_array_bytes_go(right, acc)
      middle = Equal.cong(List<&2, U32>, List<&2, U32>,
        xs => Output.bytes.go(ProofTree.to_array(left), xs),
        Output.bytes.go(ProofTree.to_array(right), acc),
        ProofTree.bytes.go(right, acc), right_proof)
      left_proof = tree_to_array_bytes_go(left,
        ProofTree.bytes.go(right, acc))
      Equal.trans(List<&2, U32>,
        Output.bytes.go(ProofTree.to_array(left),
          Output.bytes.go(ProofTree.to_array(right), acc)),
        Output.bytes.go(ProofTree.to_array(left),
          ProofTree.bytes.go(right, acc)),
        ProofTree.bytes.go(left,
          ProofTree.bytes.go(right, acc)),
        middle, left_proof)

def Laws.proof_tree_to_array_preserves_bytes(tree):
  tree_to_array_bytes_go(tree, Nil{})

def queue_pop_front_reassembles(front: List<&2, Rules.State>) ->
  {ProofQueue.reassemble(
    ProofQueue.pop_front(front, Nil{})) ==
    front : List<&2, Rules.State>}:
  match front:
    case Nil{}:
      {==}
    case head <> rest:
      {==}

def Laws.proof_queue_pop_reassembles(queue):
  match queue:
    case ProofQueue.Queue{front, back}:
      match front:
        case Nil{}:
          match back:
            case Nil{}:
              {==}
            case back_head <> back_rest:
              %queue_pop_front_reassembles(
                List.reverse(&2, Rules.State,
                  back_head <> back_rest)) :
                {ProofQueue.reassemble(ProofQueue.pop_front(
                  List.reverse(&2, Rules.State,
                    back_head <> back_rest),
                  Nil{})) == _ : List<&2, Rules.State>}
              {==}
        case head <> rest:
          match back:
            case Nil{}:
              {==}
            case back_head <> back_rest:
              {==}

def Laws.state_list_append_associative(xs, ys, zs):
  match xs:
    case Nil{}:
      {==}
    case head <> rest:
      %Laws.state_list_append_associative(rest, ys, zs) :
        {head <> List.append(&2, Rules.State, rest,
          List.append(&2, Rules.State, ys, zs)) ==
          head <> _ : List<&2, Rules.State>}
      {==}

def Laws.state_list_reverse_go_appends_acc(xs, prefix,
  suffix):
  match xs:
    case Nil{}:
      {==}
    case head <> rest:
      %Laws.state_list_reverse_go_appends_acc(rest,
        head <> prefix, suffix) :
        {List.reverse.go(&2, Rules.State, rest,
          List.append(&2, Rules.State,
            head <> prefix, suffix)) ==
          _ : List<&2, Rules.State>}
      {==}

def Laws.proof_queue_push_appends(queue, state):
  match queue:
    case ProofQueue.Queue{front, back}:
      match back:
        case Nil{}:
          {==}
        case head <> rest:
          +old_back = {head <> rest : List<&2, Rules.State>}
          +last = {state <> Nil{} : List<&2, Rules.State>}
          reverse_step = Laws.state_list_reverse_go_appends_acc(
            old_back, Nil{}, last)
          assoc = Laws.state_list_append_associative(
            front, List.reverse(&2, Rules.State, old_back),
            last)
          Equal.trans(List<&2, Rules.State>,
            ProofQueue.contents(ProofQueue.push(
              ProofQueue.Queue{front, old_back}, state)),
            List.append(&2, Rules.State, front,
              List.append(&2, Rules.State,
                List.reverse(&2, Rules.State, old_back), last)),
            List.append(&2, Rules.State,
              ProofQueue.contents(
                ProofQueue.Queue{front, old_back}), last),
            Equal.cong(List<&2, Rules.State>,
              List<&2, Rules.State>,
              xs => List.append(&2, Rules.State, front, xs),
              List.reverse.go(&2, Rules.State,
                old_back, last),
              List.append(&2, Rules.State,
                List.reverse(&2, Rules.State, old_back), last),
              reverse_step),
            assoc)

def state_list_nonempty(xs: List<&2, Rules.State>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case head <> rest:
      Unit

def reverse_go_nonempty(xs: List<&2, Rules.State>,
  +head: Rules.State, +tail: List<&2, Rules.State>) ->
  state_list_nonempty(List.reverse.go(&2, Rules.State,
    xs, head <> tail)):
  match xs:
    case Nil{}:
      Unit{}
    case next <> rest:
      reverse_go_nonempty(rest, next, head <> tail)

def pop_front_nonempty_not_none(
  front: List<&2, Rules.State>,
  nonempty: state_list_nonempty(front),
  none: Laws.QueuePopNone(
    ProofQueue.pop_front(front, Nil{}))) -> Empty:
  match front:
    case Nil{}:
      nonempty
    case head <> rest:
      none

def Laws.proof_queue_empty_pop_means_empty_contents(queue,
  none):
  match queue:
    case ProofQueue.Queue{front, back}:
      match front:
        case head <> rest:
          Empty.absurd(
            {ProofQueue.contents(
              ProofQueue.Queue{head <> rest, back}) ==
              Nil{} : List<&2, Rules.State>}, none)
        case Nil{}:
          match back:
            case Nil{}:
              {==}
            case head <> rest:
              Empty.absurd(
                {ProofQueue.contents(ProofQueue.Queue{
                  Nil{}, head <> rest}) ==
                  Nil{} : List<&2, Rules.State>},
                pop_front_nonempty_not_none(
                  List.reverse(&2, Rules.State,
                    head <> rest),
                  reverse_go_nonempty(rest, head, Nil{}),
                  none))

def Laws.retro_mark_new_preserves_full(work, state, rank,
  full):
  match work:
    case Retro.Work{won, queue, squares}:
      Laws.proof_tree_set_preserves_full(19n,
        won, ProofTree.bits19(Rules.index(state)),
        rank, full)

def Laws.retro_mark_new_keeps_squares(work, state,
  rank):
  match work:
    case Retro.Work{won, queue, squares}:
      {==}

def retro_mark_if_decision_keeps_squares(
  +work: Retro.Work, +state: Rules.State,
  +rank: U32, decision: Bool) ->
  {Laws.WorkSquares(Retro.mark.if_decision(
    work, state, rank, decision)) ==
    Laws.WorkSquares(work) : List<&2, U32>}:
  match decision:
    case True{}:
      Laws.retro_mark_new_keeps_squares(work,
        state, rank)
    case False{}:
      {==}

def Laws.retro_mark_rank_keeps_squares(work, state,
  rank):
  match work:
    case Retro.Work{won, queue, squares}:
      retro_mark_if_decision_keeps_squares(
        Retro.Work{won, queue, squares},
        state, rank,
        U32.is_eq(ProofTree.get_index(won,
          Rules.index(state)), 0))

def Laws.retro_mark_rank_preserves_square_coverage(
  work, state, rank, complete):
  equality_cast(List<&2, U32>,
    squares => @dest: U32 ->
      Laws.Truth(U32.is_lt(dest, 64)) ->
      Squares.Member(U32, dest, squares),
    Laws.WorkSquares(work),
    Laws.WorkSquares(Retro.mark.rank(work,
      state, rank)),
    Equal.sym(List<&2, U32>,
      Laws.WorkSquares(Retro.mark.rank(work,
        state, rank)),
      Laws.WorkSquares(work),
      Laws.retro_mark_rank_keeps_squares(work,
        state, rank)), complete)

def black_ready_if_keeps_squares(
  +work: Retro.Work, +state: Rules.State,
  +maximum: U32, ready: Bool) ->
  {Laws.WorkSquares(Retro.black_ready.if(
    work, state, maximum, ready)) ==
    Laws.WorkSquares(work) : List<&2, U32>}:
  match ready:
    case True{}:
      Laws.retro_mark_rank_keeps_squares(work, state,
        (maximum + 1 : U32))
    case False{}:
      {==}

def black_ready_fin_keeps_squares(
  +work: Retro.Work, +state: Rules.State,
  scan: Retro.BlackReplyScan) ->
  {Laws.WorkSquares(Retro.black_ready.fin(
    work, state, scan)) ==
    Laws.WorkSquares(work) : List<&2, U32>}:
  match scan:
    case Retro.BlackReplyScan{seen, all_won, maximum}:
      black_ready_if_keeps_squares(work, state,
        maximum, seen && all_won)

def Laws.retro_black_ready_keeps_squares(work,
  kind, state):
  match work:
    case Retro.Work{+won, queue, +squares}:
      black_ready_fin_keeps_squares(
        Retro.Work{won, queue, squares}, state,
        Retro.black_reply_scan(kind, state, won,
          squares))

def retro_predecessor_update_turn_decide_keeps_squares(
  +work: Retro.Work, +kind: U32,
  +state: Rules.State, +rank: U32, white: Bool) ->
  {Laws.WorkSquares(Retro.predecessor.update.turn.decide(
    work, kind, state, rank, white)) ==
    Laws.WorkSquares(work) : List<&2, U32>}:
  match white:
    case True{}:
      Laws.retro_mark_rank_keeps_squares(work,
        state, rank)
    case False{}:
      Laws.retro_black_ready_keeps_squares(work,
        kind, state)

def retro_predecessor_update_turn_keeps_squares(
  +work: Retro.Work, +kind: U32,
  +state: Rules.State, +turn: U32, +rank: U32) ->
  {Laws.WorkSquares(Retro.predecessor.update.turn(
    work, kind, state, turn, rank)) ==
    Laws.WorkSquares(work) : List<&2, U32>}:
  retro_predecessor_update_turn_decide_keeps_squares(
    work, kind, state, rank, U32.is_eq(turn, 0))

def retro_predecessor_update_if_keeps_squares(
  +work: Retro.Work, +kind: U32,
  +state: Rules.State, +turn: U32, +rank: U32,
  legal: Bool) ->
  {Laws.WorkSquares(Retro.predecessor.update.if(
    work, kind, state, turn, rank, legal)) ==
    Laws.WorkSquares(work) : List<&2, U32>}:
  match legal:
    case False{}:
      {==}
    case True{}:
      retro_predecessor_update_turn_keeps_squares(
        work, kind, state, turn, rank)

def Laws.retro_predecessor_update_keeps_squares(
  work, kind, previous, current, turn, rank):
  retro_predecessor_update_if_keeps_squares(
    work, kind, previous, turn, rank,
    Rules.move_to(kind, previous, current))

def Laws.retro_previous_king_keeps_squares(squares,
  work, kind, current, wk, bk, pc, rank):
  match squares:
    case Nil{}:
      {==}
    case src <> rest:
      +previous = {Rules.State{src, bk, pc, 0} : Rules.State}
      +next = Retro.predecessor.update(work, kind,
        previous, current, 0, rank)
      Equal.trans(List<&2, U32>,
        Laws.WorkSquares(Retro.previous_king.go(
          rest, kind, current, wk, bk, pc,
          rank, next)),
        Laws.WorkSquares(next),
        Laws.WorkSquares(work),
        Laws.retro_previous_king_keeps_squares(
          rest, next, kind, current, wk, bk, pc,
          rank),
        Laws.retro_predecessor_update_keeps_squares(
          work, kind, previous, current, 0, rank))

def Laws.retro_previous_piece_keeps_squares(squares,
  work, kind, current, wk, bk, pc, rank):
  match squares:
    case Nil{}:
      {==}
    case src <> rest:
      +previous = {Rules.State{wk, bk, src, 0} : Rules.State}
      +next = Retro.predecessor.update(work, kind,
        previous, current, 0, rank)
      Equal.trans(List<&2, U32>,
        Laws.WorkSquares(Retro.previous_piece.go(
          rest, kind, current, wk, bk, pc,
          rank, next)),
        Laws.WorkSquares(next),
        Laws.WorkSquares(work),
        Laws.retro_previous_piece_keeps_squares(
          rest, next, kind, current, wk, bk, pc,
          rank),
        Laws.retro_predecessor_update_keeps_squares(
          work, kind, previous, current, 0, rank))

def Laws.retro_previous_black_keeps_squares(squares,
  work, kind, current, wk, bk, pc, rank):
  match squares:
    case Nil{}:
      {==}
    case src <> rest:
      +previous = {Rules.State{wk, src, pc, 1} : Rules.State}
      +next = Retro.predecessor.update(work, kind,
        previous, current, 1, rank)
      Equal.trans(List<&2, U32>,
        Laws.WorkSquares(Retro.previous_black.go(
          rest, kind, current, wk, bk, pc,
          rank, next)),
        Laws.WorkSquares(next),
        Laws.WorkSquares(work),
        Laws.retro_previous_black_keeps_squares(
          rest, next, kind, current, wk, bk, pc,
          rank),
        Laws.retro_predecessor_update_keeps_squares(
          work, kind, previous, current, 1, rank))

def retro_previous_two_keeps_squares(
  +work: Retro.Work, +squares: List<&2, U32>,
  +kind: U32,
  +wk: U32, +bk: U32, +pc: U32,
  +rank: U32) ->
  {Laws.WorkSquares(Retro.predecessors.choose(
    work, squares, kind, wk, bk, pc, rank,
    False{}, True{})) ==
    Laws.WorkSquares(work) : List<&2, U32>}:
  +state = {Rules.State{wk, bk, pc, 1} : Rules.State}
  +next = Retro.previous_king.go(squares, kind,
    state, wk, bk, pc, rank, work)
  Equal.trans(List<&2, U32>,
    Laws.WorkSquares(Retro.previous_piece.go(
      squares, kind, state, wk, bk, pc,
      rank, next)),
    Laws.WorkSquares(next),
    Laws.WorkSquares(work),
    Laws.retro_previous_piece_keeps_squares(
      squares, next, kind, state, wk, bk, pc,
      rank),
    Laws.retro_previous_king_keeps_squares(
      squares, work, kind, state, wk, bk, pc,
      rank))

def retro_predecessors_choose_keeps_squares(
  +work: Retro.Work, +squares: List<&2, U32>,
  +kind: U32,
  +wk: U32, +bk: U32, +pc: U32,
  +rank: U32, white: Bool, black: Bool) ->
  {Laws.WorkSquares(Retro.predecessors.choose(
    work, squares, kind, wk, bk, pc, rank,
    white, black)) ==
    Laws.WorkSquares(work) : List<&2, U32>}:
  match white:
    case True{}:
      Laws.retro_previous_black_keeps_squares(
        squares, work, kind,
        Rules.State{wk, bk, pc, 0}, wk, bk, pc,
        rank)
    case False{}:
      match black:
        case True{}:
          retro_previous_two_keeps_squares(
            work, squares, kind, wk, bk, pc, rank)
        case False{}:
          {==}

def Laws.retro_predecessors_keep_squares(work,
  kind, current, rank):
  match work:
    case Retro.Work{won, queue, +squares}:
      match current:
        case Rules.State{wk, bk, pc, turn}:
          retro_predecessors_choose_keeps_squares(
            Retro.Work{won, queue, squares},
            squares, kind, wk, bk, pc, rank,
            U32.is_eq(turn, 0), U32.is_eq(turn, 1))

def Laws.retro_predecessors_preserve_square_coverage(
  work, kind, current, rank, complete):
  equality_cast(List<&2, U32>,
    squares => @dest: U32 ->
      Laws.Truth(U32.is_lt(dest, 64)) ->
      Squares.Member(U32, dest, squares),
    Laws.WorkSquares(work),
    Laws.WorkSquares(Retro.predecessors(work,
      kind, current, rank)),
    Equal.sym(List<&2, U32>,
      Laws.WorkSquares(Retro.predecessors(work,
        kind, current, rank)),
      Laws.WorkSquares(work),
      Laws.retro_predecessors_keep_squares(work,
        kind, current, rank)), complete)

def Laws.retro_mark_new_writes_rank(work, state, rank):
  match work:
    case Retro.Work{won, queue, squares}:
      Laws.proof_tree_index_read_after_write(won,
        Rules.index(state), rank)

def Laws.retro_mark_new_enqueues(work, state, rank):
  match work:
    case Retro.Work{won, queue, squares}:
      Laws.proof_queue_push_appends(queue, state)

def Laws.retro_mark_new_keeps_other_rank(work, state,
  other, rank, full, different):
  match work:
    case Retro.Work{won, queue, squares}:
      Laws.proof_tree_write_preserves_other(19n,
        won, ProofTree.bits19(Rules.index(state)),
        ProofTree.bits19(Rules.index(other)), rank,
        full, different)

def Laws.retro_mark_decision_rank(work, state, rank,
  old, decision, observed):
  match decision:
    case True{}:
      Laws.retro_mark_new_writes_rank(work, state, rank)
    case False{}:
      observed

def Laws.retro_mark_rank_value(work, state, rank):
  match work:
    case Retro.Work{won, queue, squares}:
      Laws.retro_mark_decision_rank(
        Retro.Work{won, queue, squares}, state, rank,
        ProofTree.get_index(won, Rules.index(state)),
        U32.is_eq(ProofTree.get_index(won,
          Rules.index(state)), 0), {==})

def Laws.retro_mark_decision_queue(work, state, rank,
  decision):
  match decision:
    case True{}:
      Laws.retro_mark_new_enqueues(work, state, rank)
    case False{}:
      {==}

def Laws.retro_mark_rank_queue(work, state, rank):
  match work:
    case Retro.Work{won, queue, squares}:
      Laws.retro_mark_decision_queue(
        Retro.Work{won, queue, squares}, state, rank,
        U32.is_eq(ProofTree.get_index(won,
          Rules.index(state)), 0))

def retro_take_fin_reassembles(won: ProofTree.Tree,
  squares: List<&2, U32>,
  read: ProofQueue.Queue & Maybe<&2, Rules.State>) ->
  {Laws.WorkTakeReassemble(
    Retro.take.fin(won, squares, read)) ==
    ProofQueue.reassemble(read) : List<&2, Rules.State>}:
  match read:
    case (queue, None{}):
      {==}
    case (queue, Some{state}):
      {==}

def retro_take_fin_keeps_squares(won: ProofTree.Tree,
  squares: List<&2, U32>,
  read: ProofQueue.Queue & Maybe<&2, Rules.State>) ->
  {Laws.WorkTakeSquares(Retro.take.fin(won,
    squares, read)) == squares : List<&2, U32>}:
  match read:
    case (queue, state):
      {==}

def Laws.retro_take_keeps_squares(work):
  match work:
    case Retro.Work{won, queue, squares}:
      retro_take_fin_keeps_squares(won, squares,
        ProofQueue.pop(queue))

def Laws.retro_marked_keeps_squares(work, index):
  match work:
    case Retro.Work{won, queue, squares}:
      {==}

def Laws.retro_propagate_rank_keeps_squares(kind,
  state, read):
  match read:
    case (work, rank):
      Laws.retro_predecessors_keep_squares(work,
        kind, state, (rank + 1 : U32))

def retro_propagate_consume_some_keeps_squares(
  +kind: U32, +work: Retro.Work,
  +state: Rules.State, marked: Retro.Work & U32,
  prior: {Laws.WorkRankReadSquares(marked) ==
    Laws.WorkSquares(work) : List<&2, U32>}) ->
  {Laws.WorkSquares(Retro.propagate.rank(
    kind, state, marked)) ==
    Laws.WorkSquares(work) : List<&2, U32>}:
  match marked:
    case (marked_work, rank):
      Equal.trans(List<&2, U32>,
        Laws.WorkSquares(Retro.propagate.rank(kind,
          state, (marked_work, rank))),
        Laws.WorkSquares(marked_work),
        Laws.WorkSquares(work),
        Laws.retro_propagate_rank_keeps_squares(
          kind, state, (marked_work, rank)),
        prior)

def Laws.retro_propagate_consume_keeps_squares(kind,
  read):
  match read:
    case (+work, None{}):
      {==}
    case (+work, Some{+state}):
      retro_propagate_consume_some_keeps_squares(
        kind, work, state,
        Retro.marked(work, Rules.index(state)),
        Laws.retro_marked_keeps_squares(work,
          Rules.index(state)))

def Laws.retro_propagate_step_keeps_squares(kind,
  work):
  Equal.trans(List<&2, U32>,
    Laws.WorkSquares(Retro.propagate.consume(kind,
      Retro.take(work))),
    Laws.WorkTakeSquares(Retro.take(work)),
    Laws.WorkSquares(work),
    Laws.retro_propagate_consume_keeps_squares(
      kind, Retro.take(work)),
    Laws.retro_take_keeps_squares(work))

def Laws.retro_propagate_go_keeps_squares(fuel,
  kind, work):
  match fuel:
    case 0n:
      {==}
    case 1n++rest:
      +next = Retro.propagate.step(kind, work)
      Equal.trans(List<&2, U32>,
        Laws.WorkSquares(Retro.propagate.go(rest,
          kind, next)),
        Laws.WorkSquares(next),
        Laws.WorkSquares(work),
        Laws.retro_propagate_go_keeps_squares(
          rest, kind, next),
        Laws.retro_propagate_step_keeps_squares(
          kind, work))

def Laws.retro_propagate_go_preserves_square_coverage(
  fuel, kind, work, complete):
  equality_cast(List<&2, U32>,
    squares => @dest: U32 ->
      Laws.Truth(U32.is_lt(dest, 64)) ->
      Squares.Member(U32, dest, squares),
    Laws.WorkSquares(work),
    Laws.WorkSquares(Retro.propagate.go(fuel,
      kind, work)),
    Equal.sym(List<&2, U32>,
      Laws.WorkSquares(Retro.propagate.go(fuel,
        kind, work)),
      Laws.WorkSquares(work),
      Laws.retro_propagate_go_keeps_squares(fuel,
        kind, work)), complete)

def retro_init_state_mate_keeps_squares(
  +work: Retro.Work, +state: Rules.State,
  mate: Bool) ->
  {Laws.WorkSquares(Retro.init_state.mate(work,
    state, mate)) ==
    Laws.WorkSquares(work) : List<&2, U32>}:
  match mate:
    case True{}:
      Laws.retro_mark_rank_keeps_squares(work,
        state, 1)
    case False{}:
      {==}

def retro_init_state_black_keeps_squares(
  +work: Retro.Work, +kind: U32, +index: U32,
  +wk: U32, +bk: U32, +pc: U32) ->
  {Laws.WorkSquares(Retro.init_state.black(work,
    kind, index, wk, bk, pc)) ==
    Laws.WorkSquares(work) : List<&2, U32>}:
  match work:
    case Retro.Work{won, queue, +squares}:
      retro_init_state_mate_keeps_squares(
        Retro.Work{won, queue, squares},
        Rules.State{wk, bk, pc, 1},
        Bool.not(Retro.black_has_move(kind,
          Rules.State{wk, bk, pc, 1}, squares)) &&
          Rules.attacks(kind, pc, bk, wk))

def retro_init_state_black_if_keeps_squares(
  +work: Retro.Work, +kind: U32, +index: U32,
  +wk: U32, +bk: U32, +pc: U32, black: Bool) ->
  {Laws.WorkSquares(Retro.init_state.black.if(
    work, kind, index, wk, bk, pc, black)) ==
    Laws.WorkSquares(work) : List<&2, U32>}:
  match black:
    case True{}:
      retro_init_state_black_keeps_squares(
        work, kind, index, wk, bk, pc)
    case False{}:
      {==}

def retro_init_state_valid_keeps_squares(
  +work: Retro.Work, +kind: U32,
  +index: U32, state: Rules.State) ->
  {Laws.WorkSquares(Retro.init_state.valid(
    work, kind, index, state)) ==
    Laws.WorkSquares(work) : List<&2, U32>}:
  match state:
    case Rules.State{wk, bk, pc, turn}:
      retro_init_state_black_if_keeps_squares(
        work, kind, index, wk, bk, pc,
        U32.is_eq(turn, 1))

def retro_init_state_if_keeps_squares(
  +work: Retro.Work, +kind: U32,
  +index: U32, +state: Rules.State,
  valid: Bool) ->
  {Laws.WorkSquares(Retro.init_state.if(
    work, kind, index, state, valid)) ==
    Laws.WorkSquares(work) : List<&2, U32>}:
  match valid:
    case True{}:
      retro_init_state_valid_keeps_squares(
        work, kind, index, state)
    case False{}:
      {==}

def Laws.retro_init_state_keeps_squares(work,
  kind, index):
  +state = Rules.decode(index)
  retro_init_state_if_keeps_squares(work, kind,
    index, state, Rules.valid(kind, state))

def Laws.retro_init_go_keeps_squares(fuel,
  work, kind, index):
  match fuel:
    case 0n:
      {==}
    case 1n++rest:
      +next = Retro.init_state(work, kind, index)
      Equal.trans(List<&2, U32>,
        Laws.WorkSquares(Retro.init.go(rest,
          kind, (index + 1 : U32), next)),
        Laws.WorkSquares(next),
        Laws.WorkSquares(work),
        Laws.retro_init_go_keeps_squares(rest,
          next, kind, (index + 1 : U32)),
        Laws.retro_init_state_keeps_squares(work,
          kind, index))

def Laws.retro_init_go_preserves_square_coverage(
  fuel, work, kind, index, complete):
  equality_cast(List<&2, U32>,
    squares => @dest: U32 ->
      Laws.Truth(U32.is_lt(dest, 64)) ->
      Squares.Member(U32, dest, squares),
    Laws.WorkSquares(work),
    Laws.WorkSquares(Retro.init.go(fuel,
      kind, index, work)),
    Equal.sym(List<&2, U32>,
      Laws.WorkSquares(Retro.init.go(fuel,
        kind, index, work)),
      Laws.WorkSquares(work),
      Laws.retro_init_go_keeps_squares(fuel,
        work, kind, index)), complete)

def Laws.retro_take_reassembles_queue(work):
  match work:
    case Retro.Work{won, queue, squares}:
      Equal.trans(List<&2, Rules.State>,
        Laws.WorkTakeReassemble(Retro.take.fin(won, squares,
          ProofQueue.pop(queue))),
        ProofQueue.reassemble(ProofQueue.pop(queue)),
        ProofQueue.contents(queue),
        retro_take_fin_reassembles(won, squares,
          ProofQueue.pop(queue)),
        Laws.proof_queue_pop_reassembles(queue))

def retro_take_fin_none(won: ProofTree.Tree,
  squares: List<&2, U32>,
  read: ProofQueue.Queue & Maybe<&2, Rules.State>,
  none: Laws.WorkTakeNone(
    Retro.take.fin(won, squares, read))) ->
  Laws.QueuePopNone(read):
  match read:
    case (queue, None{}):
      Unit{}
    case (queue, Some{state}):
      none

def Laws.retro_take_none_means_queue_empty(work, none):
  match work:
    case Retro.Work{won, queue, squares}:
      Laws.proof_queue_empty_pop_means_empty_contents(
        queue,
        retro_take_fin_none(won, squares,
          ProofQueue.pop(queue), none))

def black_consider_prior(+scan: Retro.BlackReplyScan,
  +rank: U32, capture: Bool, legal: Bool,
  after: Laws.Truth(Laws.BlackScanAll(
    Retro.black_reply_consider(scan, rank, capture, legal)))) ->
  Laws.Truth(Laws.BlackScanAll(scan)):
  match scan:
    case Retro.BlackReplyScan{seen, +all_won, maximum}:
      match legal:
        case False{}:
          after
        case True{}:
          first = and_left(all_won && Bool.not(capture),
            U32.is_ne(rank, 0), after)
          and_left(all_won, Bool.not(capture), first)

def black_consider_edge(+scan: Retro.BlackReplyScan,
  +rank: U32, +capture: Bool, legal: Bool,
  +after: Laws.Truth(Laws.BlackScanAll(
    Retro.black_reply_consider(scan, rank, capture, legal)))) ->
  Laws.Truth(legal) ->
    Laws.Truth(Bool.not(capture)) &
    Laws.Truth(U32.is_ne(rank, 0)):
  match scan:
    case Retro.BlackReplyScan{seen, +all_won, maximum}:
      match legal:
        case False{}:
          impossible => Empty.absurd(
            Laws.Truth(Bool.not(capture)) &
              Laws.Truth(U32.is_ne(rank, 0)),
            impossible)
        case True{}:
          +first = and_left(all_won && Bool.not(capture),
            U32.is_ne(rank, 0), after)
          no_capture = and_right(all_won,
            Bool.not(capture), first)
          positive = and_right(
            all_won && Bool.not(capture),
            U32.is_ne(rank, 0), after)
          legal_proof => (no_capture, positive)

def black_scan_succ_finish(rest: Nat, +kind: U32,
  +wk: U32, +bk: U32, +pc: U32, +dest: U32,
  +won: ProofTree.Tree, +scan: Retro.BlackReplyScan,
  result:
    Laws.Truth(Laws.BlackScanAll(
      Retro.black_reply_consider(scan,
        ProofTree.get_index(won, Rules.index(
          Rules.State{wk, dest, pc, 0})),
        U32.is_eq(dest, pc),
        Rules.black_move(kind, wk, bk, pc, dest)))) &
    Laws.BlackScanSegment(rest, kind, wk, bk, pc,
      (dest + 1 : U32), won)) ->
  Laws.Truth(Laws.BlackScanAll(scan)) &
  Laws.BlackScanSegment(1n+rest, kind, wk, bk, pc,
    dest, won):
  match result:
    case (+next_all, tail):
      +rank = ProofTree.get_index(won,
        Rules.index(Rules.State{wk, dest, pc, 0}))
      +capture = U32.is_eq(dest, pc)
      +legal = Rules.black_move(kind, wk, bk, pc, dest)
      prior = black_consider_prior(scan, rank, capture,
        legal, next_all)
      edge = black_consider_edge(scan, rank, capture,
        legal, next_all)
      (prior, (edge, tail))

def black_scan_all_sound_go(fuel: Nat, +kind: U32,
  +wk: U32, +bk: U32, +pc: U32, +dest: U32,
  +won: ProofTree.Tree, +scan: Retro.BlackReplyScan,
  all: Laws.Truth(Laws.BlackScanAll(
    Retro.black_reply_scan.go(fuel, kind, wk, bk, pc,
      dest, won, scan)))) ->
  Laws.Truth(Laws.BlackScanAll(scan)) &
  Laws.BlackScanSegment(fuel, kind, wk, bk, pc, dest, won):
  match fuel:
    case 0n:
      (all, Unit{})
    case 1n++rest:
      +rank = ProofTree.get_index(won,
        Rules.index(Rules.State{wk, dest, pc, 0}))
      +capture = U32.is_eq(dest, pc)
      +legal = Rules.black_move(kind, wk, bk, pc, dest)
      black_scan_succ_finish(rest, kind, wk, bk, pc,
        dest, won, scan,
        black_scan_all_sound_go(rest, kind, wk, bk, pc,
          (dest + 1 : U32), won,
          Retro.black_reply_consider(scan, rank, capture,
            legal), all))

def Laws.black_reply_scan_all_sound(fuel, kind, wk, bk,
  pc, dest, won, scan, all):
  pair_right(
    Laws.Truth(Laws.BlackScanAll(scan)),
    Laws.BlackScanSegment(fuel, kind, wk, bk, pc,
      dest, won),
    black_scan_all_sound_go(fuel, kind, wk, bk,
      pc, dest, won, scan, all))

def black_consider_complete_true(+all_won: Bool,
  +capture: Bool, +rank: U32,
  initial: Laws.Truth(all_won),
  safe: Laws.Truth(Bool.not(capture)) &
    Laws.Truth(U32.is_ne(rank, 0))) ->
  Laws.Truth(all_won && Bool.not(capture) &&
    U32.is_ne(rank, 0)):
  match safe:
    case (no_capture, positive):
      first = and_intro(all_won, Bool.not(capture),
        initial, no_capture)
      and_intro(all_won && Bool.not(capture),
        U32.is_ne(rank, 0), first, positive)

def black_consider_complete(+scan: Retro.BlackReplyScan,
  +rank: U32, +capture: Bool, legal: Bool,
  initial: Laws.Truth(Laws.BlackScanAll(scan)),
  safe: Laws.Truth(legal) ->
    Laws.Truth(Bool.not(capture)) &
    Laws.Truth(U32.is_ne(rank, 0))) ->
  Laws.Truth(Laws.BlackScanAll(
    Retro.black_reply_consider(scan, rank, capture, legal))):
  match scan:
    case Retro.BlackReplyScan{seen, +all_won, maximum}:
      match legal:
        case False{}:
          initial
        case True{}:
          black_consider_complete_true(all_won,
            capture, rank, initial, safe(Unit{}))

def Laws.black_reply_scan_all_complete(fuel, kind, wk,
  bk, pc, dest, won, scan, initial_all, segment):
  match fuel:
    case 0n:
      initial_all
    case 1n++rest:
      match segment:
        case (head_safe, tail):
          +rank = ProofTree.get_index(won,
            Rules.index(Rules.State{wk, dest, pc, 0}))
          +capture = U32.is_eq(dest, pc)
          +legal = Rules.black_move(kind, wk, bk, pc, dest)
          next_all = black_consider_complete(scan, rank,
            capture, legal, initial_all, head_safe)
          Laws.black_reply_scan_all_complete(rest,
            kind, wk, bk, pc, (dest + 1 : U32), won,
            Retro.black_reply_consider(scan, rank,
              capture, legal), next_all, tail)

def black_consider_seen_prior(+scan: Retro.BlackReplyScan,
  rank: U32, capture: Bool, legal: Bool,
  prior: Laws.Truth(Laws.BlackScanSeen(scan))) ->
  Laws.Truth(Laws.BlackScanSeen(
    Retro.black_reply_consider(scan, rank, capture,
      legal))):
  match scan:
    case Retro.BlackReplyScan{seen, all_won, maximum}:
      match legal:
        case False{}:
          prior
        case True{}:
          Unit{}

def black_consider_seen_legal(+scan: Retro.BlackReplyScan,
  rank: U32, capture: Bool, legal: Bool,
  edge: Laws.Truth(legal)) ->
  Laws.Truth(Laws.BlackScanSeen(
    Retro.black_reply_consider(scan, rank, capture,
      legal))):
  match scan:
    case Retro.BlackReplyScan{seen, all_won, maximum}:
      match legal:
        case False{}:
          Empty.absurd(Laws.Truth(seen), edge)
        case True{}:
          Unit{}

def black_scan_seen_preserved_go(fuel: Nat,
  +kind: U32, +wk: U32, +bk: U32, +pc: U32,
  +dest: U32, +won: ProofTree.Tree,
  +scan: Retro.BlackReplyScan,
  prior: Laws.Truth(Laws.BlackScanSeen(scan))) ->
  Laws.Truth(Laws.BlackScanSeen(
    Retro.black_reply_scan.go(fuel, kind, wk, bk,
      pc, dest, won, scan))):
  match fuel:
    case 0n:
      prior
    case 1n+rest:
      +rank = ProofTree.get_index(won,
        Rules.index(Rules.State{wk, dest, pc, 0}))
      +capture = U32.is_eq(dest, pc)
      +legal = Rules.black_move(kind, wk, bk, pc, dest)
      black_scan_seen_preserved_go(rest, kind, wk, bk,
        pc, (dest + 1 : U32), won,
        Retro.black_reply_consider(scan, rank, capture,
          legal),
        black_consider_seen_prior(scan, rank, capture,
          legal, prior))

def Laws.black_reply_scan_seen_complete(fuel, kind,
  wk, bk, pc, dest, won, scan, legal):
  match fuel:
    case 0n:
      match legal:
    case 1n+rest:
      match legal:
        case Inl{head}:
          +rank = ProofTree.get_index(won,
            Rules.index(Rules.State{wk, dest, pc, 0}))
          +capture = U32.is_eq(dest, pc)
          +edge = Rules.black_move(kind, wk, bk, pc, dest)
          black_scan_seen_preserved_go(rest, kind,
            wk, bk, pc, (dest + 1 : U32), won,
            Retro.black_reply_consider(scan, rank,
              capture, edge),
            black_consider_seen_legal(scan, rank,
              capture, edge, head))
        case Inr{tail}:
          +rank = ProofTree.get_index(won,
            Rules.index(Rules.State{wk, dest, pc, 0}))
          +capture = U32.is_eq(dest, pc)
          +edge = Rules.black_move(kind, wk, bk, pc, dest)
          Laws.black_reply_scan_seen_complete(rest,
            kind, wk, bk, pc, (dest + 1 : U32), won,
            Retro.black_reply_consider(scan, rank,
              capture, edge), tail)

def black_has_move_true_stays_true(fuel: Nat,
  +kind: U32, +wk: U32, +bk: U32, +pc: U32,
  +dest: U32) ->
  Laws.Truth(Retro.black_has_move.go(fuel,
    kind, wk, bk, pc, dest, True{})):
  match fuel:
    case 0n:
      Unit{}
    case 1n+rest:
      black_has_move_true_stays_true(rest,
        kind, wk, bk, pc, (dest + 1 : U32))

def black_has_move_head_decision(rest: Nat,
  +kind: U32, +wk: U32, +bk: U32, +pc: U32,
  +dest: U32, found: Bool, legal: Bool,
  head: Laws.Truth(legal)) ->
  Laws.Truth(Retro.black_has_move.go(rest,
    kind, wk, bk, pc, (dest + 1 : U32),
    found || legal)):
  match found:
    case False{}:
      match legal:
        case False{}:
          Empty.absurd(
            Laws.Truth(Retro.black_has_move.go(rest,
              kind, wk, bk, pc, (dest + 1 : U32),
              False{})), head)
        case True{}:
          black_has_move_true_stays_true(rest,
            kind, wk, bk, pc, (dest + 1 : U32))
    case True{}:
      black_has_move_true_stays_true(rest,
        kind, wk, bk, pc, (dest + 1 : U32))

def Laws.black_has_move_complete(fuel, kind, wk, bk,
  pc, dest, found, legal):
  match fuel:
    case 0n:
      match legal:
    case 1n+rest:
      match legal:
        case Inl{head}:
          black_has_move_head_decision(rest, kind,
            wk, bk, pc, dest, found,
            Rules.black_move(kind, wk, bk, pc, dest), head)
        case Inr{tail}:
          Laws.black_has_move_complete(rest, kind,
            wk, bk, pc, (dest + 1 : U32),
            found || Rules.black_move(kind, wk, bk,
              pc, dest), tail)

def truth_and_not(+value: Bool,
  yes: Laws.Truth(value),
  no: Laws.Truth(Bool.not(value))) -> Empty:
  match value:
    case True{}:
      no
    case False{}:
      yes

def Laws.legal_quiet_black_destination_is_a_rules_move(
  kind, wk, bk, pc, dest, valid, legal, quiet):
  +king = Rules.king_step(bk, dest)
  +safe = Bool.not(Position.kings_touch(wk, dest))
  +capture = U32.is_eq(dest, pc)
  +target = Rules.valid(kind,
    Rules.State{wk, dest, pc, 0})
  +first = and_left(king && safe,
    capture || target, legal)
  king_step = and_left(king, safe, first)
  escape = and_right(king && safe,
    capture || target, legal)
  target_valid = or_cases(Laws.Truth(target),
    capture, target, escape,
    captured => Empty.absurd(Laws.Truth(target),
      truth_and_not(capture, captured, quiet)),
    accepted => accepted)
  pair = and_intro(
    Rules.valid(kind, Rules.State{wk, bk, pc, 1}),
    target, valid, target_valid)
  pair = and_intro(
    Rules.valid(kind, Rules.State{wk, bk, pc, 1}) &&
      target, U32.is_eq(wk, wk), pair,
    Laws.u32_equality_reflexive(wk))
  pair = and_intro(
    Rules.valid(kind, Rules.State{wk, bk, pc, 1}) &&
      target && U32.is_eq(wk, wk),
    U32.is_eq(pc, pc), pair,
    Laws.u32_equality_reflexive(pc))
  and_intro(
    Rules.valid(kind, Rules.State{wk, bk, pc, 1}) &&
      target && U32.is_eq(wk, wk) &&
      U32.is_eq(pc, pc),
    king, pair, king_step)

def Laws.black_rules_move_is_a_legal_destination(
  kind, wk, bk, pc, dest, move):
  +source = Rules.valid(kind,
    Rules.State{wk, bk, pc, 1})
  +target = Rules.valid(kind,
    Rules.State{wk, dest, pc, 0})
  +same_wk = U32.is_eq(wk, wk)
  +same_pc = U32.is_eq(pc, pc)
  +king = Rules.king_step(bk, dest)
  first3 = and_left(source && target && same_wk,
    same_pc, and_left(source && target && same_wk &&
      same_pc, king, move))
  first2 = and_left(source && target,
    same_wk, first3)
  +target_valid = and_right(source, target,
    first2)
  king_step = and_right(source && target && same_wk &&
    same_pc, king, move)
  safe = Laws.legal_three_man_position_has_no_black_king_check(
    kind, wk, dest, pc, 0, target_valid)
  capture_or_target = or_right(U32.is_eq(dest, pc),
    target, target_valid)
  first = and_intro(king,
    Bool.not(Position.kings_touch(wk, dest)),
    king_step, safe)
  and_intro(king &&
    Bool.not(Position.kings_touch(wk, dest)),
    U32.is_eq(dest, pc) || target,
    first, capture_or_target)

def Laws.black_has_move_false_excludes_legal(fuel,
  kind, wk, bk, pc, dest, absent):
  legal => truth_and_not(
    Retro.black_has_move.go(fuel, kind, wk, bk, pc,
      dest, False{}),
    Laws.black_has_move_complete(fuel,
      kind, wk, bk, pc, dest, False{}, legal),
    absent)

def black_no_legal_succ(rest: Nat, +kind: U32,
  +wk: U32, +bk: U32, +pc: U32, +dest: U32,
  legal: Bool,
  no_legal: (Laws.Truth(legal) |
    Laws.BlackLegalSegment(rest, kind, wk, bk, pc,
      (dest + 1 : U32))) -> Empty,
  recurse:
    (Laws.BlackLegalSegment(rest, kind, wk, bk, pc,
      (dest + 1 : U32)) -> Empty) ->
    Laws.Truth(Bool.not(Retro.black_has_move.go(rest,
      kind, wk, bk, pc, (dest + 1 : U32),
      False{})))) ->
  Laws.Truth(Bool.not(Retro.black_has_move.go(rest,
    kind, wk, bk, pc, (dest + 1 : U32),
    False{} || legal))):
  match legal:
    case True{}:
      Empty.absurd(
        Laws.Truth(Bool.not(Retro.black_has_move.go(
          rest, kind, wk, bk, pc, (dest + 1 : U32),
          True{}))),
        no_legal(Inl{Unit{}}))
    case False{}:
      recurse(tail => no_legal(Inr{tail}))

def black_has_move_false_no_legal_go(fuel: Nat,
  +kind: U32, +wk: U32, +bk: U32, +pc: U32,
  +dest: U32,
  no_legal: Laws.BlackLegalSegment(fuel,
    kind, wk, bk, pc, dest) -> Empty) ->
  Laws.Truth(Bool.not(Retro.black_has_move.go(fuel,
    kind, wk, bk, pc, dest, False{}))):
  match fuel:
    case 0n:
      Unit{}
    case 1n++rest:
      black_no_legal_succ(rest, kind, wk, bk, pc,
        dest, Rules.black_move(kind, wk, bk, pc,
          dest), no_legal,
        tail_no => black_has_move_false_no_legal_go(rest,
          kind, wk, bk, pc, (dest + 1 : U32), tail_no))

def Laws.black_has_move_false_if_no_legal(fuel,
  kind, wk, bk, pc, dest, no_legal):
  black_has_move_false_no_legal_go(fuel,
    kind, wk, bk, pc, dest, no_legal)

def black_square_scan_sound_cons(
  +kind: U32, +wk: U32, +bk: U32, +pc: U32,
  +dest: U32, +won: ProofTree.Tree,
  +scan: Retro.BlackReplyScan,
  rest: List<&2, U32>,
  result:
    Laws.Truth(Laws.BlackScanAll(
      Retro.black_reply_consider(scan,
        ProofTree.get_index(won,
          Rules.index(Rules.State{wk, dest, pc, 0})),
        U32.is_eq(dest, pc),
        Rules.black_move(kind, wk, bk, pc, dest)))) &
    Laws.BlackScanSquares(rest, kind, wk, bk, pc, won)) ->
  Laws.Truth(Laws.BlackScanAll(scan)) &
  Laws.BlackScanSquares(dest <> rest, kind, wk, bk,
    pc, won):
  match result:
    case (+next_all, tail_safe):
      +rank = ProofTree.get_index(won,
        Rules.index(Rules.State{wk, dest, pc, 0}))
      +capture = U32.is_eq(dest, pc)
      +legal = Rules.black_move(kind, wk, bk, pc, dest)
      (black_consider_prior(scan, rank, capture,
         legal, next_all),
       (black_consider_edge(scan, rank, capture,
          legal, next_all), tail_safe))

def black_square_scan_sound_go(squares: List<&2, U32>,
  +kind: U32, +wk: U32, +bk: U32, +pc: U32,
  +won: ProofTree.Tree, +scan: Retro.BlackReplyScan,
  all: Laws.Truth(Laws.BlackScanAll(
    Retro.black_reply_scan.squares(kind, wk, bk, pc,
      squares, won, scan)))) ->
  Laws.Truth(Laws.BlackScanAll(scan)) &
  Laws.BlackScanSquares(squares, kind, wk, bk, pc, won):
  match squares:
    case Nil{}:
      (all, Unit{})
    case +dest <> +rest:
      +rank = ProofTree.get_index(won,
        Rules.index(Rules.State{wk, dest, pc, 0}))
      +capture = U32.is_eq(dest, pc)
      +legal = Rules.black_move(kind, wk, bk, pc, dest)
      black_square_scan_sound_cons(kind, wk, bk, pc,
        dest, won, scan, rest,
        black_square_scan_sound_go(rest, kind,
          wk, bk, pc, won,
          Retro.black_reply_consider(scan, rank,
            capture, legal), all))

def Laws.black_reply_square_scan_all_sound(squares,
  kind, wk, bk, pc, won, scan, all):
  pair_right(Laws.Truth(Laws.BlackScanAll(scan)),
    Laws.BlackScanSquares(squares, kind, wk, bk, pc,
      won),
    black_square_scan_sound_go(squares, kind, wk,
      bk, pc, won, scan, all))

def Laws.black_reply_square_scan_all_complete(squares,
  kind, wk, bk, pc, won, scan, initial, safe):
  match squares:
    case Nil{}:
      initial
    case +dest <> rest:
      match safe:
        case (head_safe, tail_safe):
          +rank = ProofTree.get_index(won,
            Rules.index(Rules.State{wk, dest, pc, 0}))
          +capture = U32.is_eq(dest, pc)
          +legal = Rules.black_move(kind, wk, bk, pc,
            dest)
          next_all = black_consider_complete(scan,
            rank, capture, legal, initial, head_safe)
          Laws.black_reply_square_scan_all_complete(
            rest, kind, wk, bk, pc, won,
            Retro.black_reply_consider(scan, rank,
              capture, legal), next_all, tail_safe)

def black_square_seen_preserved(squares: List<&2, U32>,
  +kind: U32, +wk: U32, +bk: U32, +pc: U32,
  +won: ProofTree.Tree, +scan: Retro.BlackReplyScan,
  prior: Laws.Truth(Laws.BlackScanSeen(scan))) ->
  Laws.Truth(Laws.BlackScanSeen(
    Retro.black_reply_scan.squares(kind, wk, bk, pc,
      squares, won, scan))):
  match squares:
    case Nil{}:
      prior
    case +dest <> rest:
      +rank = ProofTree.get_index(won,
        Rules.index(Rules.State{wk, dest, pc, 0}))
      +capture = U32.is_eq(dest, pc)
      +legal = Rules.black_move(kind, wk, bk, pc, dest)
      black_square_seen_preserved(rest, kind, wk, bk,
        pc, won,
        Retro.black_reply_consider(scan, rank,
          capture, legal),
        black_consider_seen_prior(scan, rank,
          capture, legal, prior))

def Laws.black_reply_square_scan_seen_complete(squares,
  kind, wk, bk, pc, won, scan, legal):
  match squares:
    case Nil{}:
      match legal:
    case +dest <> rest:
      match legal:
        case Inl{head}:
          +rank = ProofTree.get_index(won,
            Rules.index(Rules.State{wk, dest, pc, 0}))
          +capture = U32.is_eq(dest, pc)
          +edge = Rules.black_move(kind, wk, bk, pc, dest)
          black_square_seen_preserved(rest, kind,
            wk, bk, pc, won,
            Retro.black_reply_consider(scan, rank,
              capture, edge),
            black_consider_seen_legal(scan, rank,
              capture, edge, head))
        case Inr{tail}:
          +rank = ProofTree.get_index(won,
            Rules.index(Rules.State{wk, dest, pc, 0}))
          +capture = U32.is_eq(dest, pc)
          +edge = Rules.black_move(kind, wk, bk, pc, dest)
          Laws.black_reply_square_scan_seen_complete(
            rest, kind, wk, bk, pc, won,
            Retro.black_reply_consider(scan, rank,
              capture, edge), tail)

def black_square_has_move_true(squares: List<&2, U32>,
  +kind: U32, +wk: U32, +bk: U32, +pc: U32) ->
  Laws.Truth(Retro.black_has_move.squares(kind,
    wk, bk, pc, squares, True{})):
  match squares:
    case Nil{}:
      Unit{}
    case dest <> rest:
      black_square_has_move_true(rest, kind, wk, bk,
        pc)

def black_square_has_move_head(rest: List<&2, U32>,
  +kind: U32, +wk: U32, +bk: U32, +pc: U32,
  found: Bool, legal: Bool,
  head: Laws.Truth(legal)) ->
  Laws.Truth(Retro.black_has_move.squares(kind,
    wk, bk, pc, rest, found || legal)):
  match found:
    case False{}:
      match legal:
        case False{}:
          Empty.absurd(
            Laws.Truth(Retro.black_has_move.squares(
              kind, wk, bk, pc, rest, False{})), head)
        case True{}:
          black_square_has_move_true(rest, kind,
            wk, bk, pc)
    case True{}:
      black_square_has_move_true(rest, kind,
        wk, bk, pc)

def Laws.black_has_move_squares_complete(squares,
  kind, wk, bk, pc, found, legal):
  match squares:
    case Nil{}:
      match legal:
    case dest <> rest:
      match legal:
        case Inl{head}:
          black_square_has_move_head(rest, kind,
            wk, bk, pc, found,
            Rules.black_move(kind, wk, bk, pc, dest),
            head)
        case Inr{tail}:
          Laws.black_has_move_squares_complete(rest,
            kind, wk, bk, pc,
            found || Rules.black_move(kind, wk,
              bk, pc, dest), tail)

def black_has_move_squares_sound_head(
  rest: List<&2, U32>, +kind: U32,
  +wk: U32, +bk: U32, +pc: U32,
  +dest: U32, edge: Bool,
  equality: {edge == Rules.black_move(kind,
    wk, bk, pc, dest) : Bool},
  yes: Laws.Truth(Retro.black_has_move.squares(
    kind, wk, bk, pc, rest, edge)),
  recurse: Laws.Truth(Retro.black_has_move.squares(
    kind, wk, bk, pc, rest, False{})) ->
    Laws.BlackLegalSquares(rest, kind, wk, bk, pc)) ->
  Laws.BlackLegalSquares(dest <> rest, kind,
    wk, bk, pc):
  match edge:
    case True{}:
      Inl{equality_cast(Bool, Laws.Truth,
        True{}, Rules.black_move(kind, wk, bk, pc,
          dest), equality, Unit{})}
    case False{}:
      Inr{recurse(yes)}

def Laws.black_has_move_squares_sound(squares,
  kind, wk, bk, pc, yes):
  match squares:
    case Nil{}:
      match yes:
    case +dest <> +rest:
      black_has_move_squares_sound_head(rest,
        kind, wk, bk, pc, dest,
        Rules.black_move(kind, wk, bk, pc, dest),
        {==}, yes,
        tail_yes => Laws.black_has_move_squares_sound(
          rest, kind, wk, bk, pc, tail_yes))

def Laws.black_legal_squares_has_witness(squares,
  kind, wk, bk, pc, legal):
  match squares:
    case Nil{}:
      match legal:
    case dest <> rest:
      match legal:
        case Inl{head}:
          (dest, head)
        case Inr{tail}:
          Laws.black_legal_squares_has_witness(
            rest, kind, wk, bk, pc, tail)

def black_legal_witness_is_a_game_move_fin(
  +kind: U32, +wk: U32, +bk: U32,
  +pc: U32, +dest: U32,
  valid: Laws.Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, 1})),
  legal: Laws.Truth(Rules.black_move(kind,
    wk, bk, pc, dest)),
  capture: Bool,
  equality: {capture == U32.is_eq(dest, pc) : Bool}) ->
  WDL.BlackHasMove(kind, wk, bk, pc):
  match capture:
    case True{}:
      captured = equality_cast(Bool, Laws.Truth,
        True{}, U32.is_eq(dest, pc),
        equality, Unit{})
      same = Laws.u32_equality_reflects_identity(
        dest, pc, captured)
      capture_move = equality_cast(U32,
        square => Laws.Truth(Rules.black_move(
          kind, wk, bk, pc, square)),
        dest, pc, same, legal)
      (WDL.KingsOnly{},
        Laws.legal_black_capture_is_a_draw_exit(
          kind, wk, bk, pc, valid,
          capture_move))
    case False{}:
      quiet = equality_cast(Bool,
        value => Laws.Truth(Bool.not(value)),
        False{}, U32.is_eq(dest, pc),
        equality, Unit{})
      ordinary = Laws.legal_quiet_black_destination_is_a_rules_move(
        kind, wk, bk, pc, dest, valid, legal,
        quiet)
      (WDL.White{kind, wk, dest, pc},
        Laws.same_class_black_move_is_a_game_move(
          kind, wk, bk, pc, wk, dest, pc,
          ordinary))

def Laws.black_legal_witness_is_a_game_move(
  kind, wk, bk, pc, valid, legal):
  match legal:
    case (+dest, move):
      black_legal_witness_is_a_game_move_fin(
        kind, wk, bk, pc, dest, valid, move,
        U32.is_eq(dest, pc), {==})

def black_game_white_move_to_legal_destination(
  +kind: U32, +wk: U32, +bk: U32,
  +pc: U32, +kind2: U32, +wk2: U32,
  +bk2: U32, +pc2: U32,
  game_move: WDL.Truth(WDL.move(
    WDL.Black{kind, wk, bk, pc},
    WDL.White{kind2, wk2, bk2, pc2}))) ->
  Laws.BlackLegalWitness(kind, wk, bk, pc):
  +ordinary = and_right(U32.is_eq(kind, kind2),
    Rules.move_to(kind,
      Rules.State{wk, bk, pc, 1},
      Rules.State{wk2, bk2, pc2, 0}),
    wdl_truth_to_laws_truth(WDL.move(
      WDL.Black{kind, wk, bk, pc},
      WDL.White{kind2, wk2, bk2, pc2}),
      game_move))
  +shape = Laws.every_black_move_has_reverse_search_shape(
    kind, wk, bk, pc, wk2, bk2, pc2,
    ordinary)
  wk_equal = and_left(U32.is_eq(wk, wk2),
    U32.is_eq(pc, pc2), shape)
  pc_equal = and_right(U32.is_eq(wk, wk2),
    U32.is_eq(pc, pc2), shape)
  wk_same = Laws.u32_equality_reflects_identity(
    wk, wk2, wk_equal)
  pc_same = Laws.u32_equality_reflects_identity(
    pc, pc2, pc_equal)
  moved_wk = equality_cast(U32,
    square => Laws.Truth(Rules.move_to(kind,
      Rules.State{wk, bk, pc, 1},
      Rules.State{square, bk2, pc2, 0})),
    wk2, wk, Equal.sym(U32, wk, wk2,
      wk_same), ordinary)
  moved_pc = equality_cast(U32,
    square => Laws.Truth(Rules.move_to(kind,
      Rules.State{wk, bk, pc, 1},
      Rules.State{wk, bk2, square, 0})),
    pc2, pc, Equal.sym(U32, pc, pc2,
      pc_same), moved_wk)
  (bk2,
    Laws.black_rules_move_is_a_legal_destination(
      kind, wk, bk, pc, bk2, moved_pc))

def Laws.game_black_move_has_legal_destination(
  kind, wk, bk, pc, game_move):
  match game_move:
    case (next, move):
      match next:
        case WDL.KingsOnly{}:
          capture = Laws.game_draw_exit_is_a_legal_black_capture(
            kind, wk, bk, pc, move)
          (pc, pair_right(Laws.Truth(Rules.valid(kind,
            Rules.State{wk, bk, pc, 1})),
            Laws.Truth(Rules.black_move(kind,
              wk, bk, pc, pc)), capture))
        case WDL.White{kind2, wk2, bk2, pc2}:
          black_game_white_move_to_legal_destination(
            kind, wk, bk, pc,
            kind2, wk2, bk2, pc2, move)
        case WDL.Black{kind2, wk2, bk2, pc2}:
          match move:
        case WDL.BareBishop{}:
          match move:
        case WDL.BareKnight{}:
          match move:

def black_consider_seen_matches_or(
  +scan: Retro.BlackReplyScan, +rank: U32,
  +capture: Bool, legal: Bool) ->
  {Laws.BlackScanSeen(Retro.black_reply_consider(
    scan, rank, capture, legal)) ==
    (Laws.BlackScanSeen(scan) || legal) : Bool}:
  match scan:
    case Retro.BlackReplyScan{seen, all_won, maximum}:
      match seen legal:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}

def Laws.black_reply_scan_seen_matches_has_move(
  squares, kind, wk, bk, pc, won, scan):
  match squares:
    case Nil{}:
      {==}
    case +dest <> +rest:
      +rank = ProofTree.get_index(won,
        Rules.index(Rules.State{wk, dest, pc, 0}))
      +capture = U32.is_eq(dest, pc)
      +legal = Rules.black_move(kind, wk, bk, pc, dest)
      +next = Retro.black_reply_consider(scan,
        rank, capture, legal)
      Equal.trans(Bool,
        Laws.BlackScanSeen(
          Retro.black_reply_scan.squares(kind,
            wk, bk, pc, rest, won, next)),
        Retro.black_has_move.squares(kind,
          wk, bk, pc, rest,
          Laws.BlackScanSeen(next)),
        Retro.black_has_move.squares(kind,
          wk, bk, pc, rest,
          Laws.BlackScanSeen(scan) || legal),
        Laws.black_reply_scan_seen_matches_has_move(
          rest, kind, wk, bk, pc, won, next),
        Equal.cong(Bool, Bool,
          found => Retro.black_has_move.squares(
            kind, wk, bk, pc, rest, found),
          Laws.BlackScanSeen(next),
          Laws.BlackScanSeen(scan) || legal,
          black_consider_seen_matches_or(scan,
            rank, capture, legal)))

def Laws.clocked_step_pawn_reset_matches_game_clock(
  kind, wk, bk, pc, dest, next, reset):
  {==}

def Laws.white_king_squares_have_witness(
  squares, kind, wk, bk, pc, next, found):
  match squares:
    case Nil{}:
      match found:
    case dest <> rest:
      match found:
        case Inl{head}:
          (dest, head)
        case Inr{later}:
          Laws.white_king_squares_have_witness(
            rest, kind, wk, bk, pc, next,
            later)

def Laws.finite_some_white_king_matches_scan(
  squares, kind, wk, bk, pc, next, found):
  match squares:
    case Nil{}:
      match found:
    case +dest <> rest:
      match found:
        case Inl{head}:
          match head:
            case (legal, yes):
              Inl{(
                wdl_truth_to_laws_truth(
                  Rules.move_to(kind,
                    Rules.State{wk, bk, pc, 0},
                    Rules.State{dest, bk, pc, 1}),
                  legal),
                wdl_truth_to_laws_truth(
                  U32.is_ne(ProofTree.get_index(next,
                    Rules.index(Rules.State{
                      dest, bk, pc, 1})), 0),
                  yes))}
        case Inr{later}:
          Inr{Laws.finite_some_white_king_matches_scan(
            rest, kind, wk, bk, pc, next,
            later)}

def Laws.white_king_scan_matches_finite_some(
  squares, kind, wk, bk, pc, next, found):
  match squares:
    case Nil{}:
      match found:
    case +dest <> rest:
      match found:
        case Inl{head}:
          match head:
            case (legal, yes):
              Inl{(
                laws_truth_to_wdl_truth(
                  Rules.move_to(kind,
                    Rules.State{wk, bk, pc, 0},
                    Rules.State{dest, bk, pc, 1}),
                  legal),
                laws_truth_to_wdl_truth(
                  U32.is_ne(ProofTree.get_index(next,
                    Rules.index(Rules.State{
                      dest, bk, pc, 1})), 0),
                  yes))}
        case Inr{later}:
          Inr{Laws.white_king_scan_matches_finite_some(
            rest, kind, wk, bk, pc, next,
            later)}

def Laws.finite_some_white_piece_matches_scan(
  squares, kind, wk, bk, pc, next, reset,
  found):
  match squares:
    case Nil{}:
      match found:
    case +dest <> rest:
      match found:
        case Inl{head}:
          match head:
            case (legal, yes):
              Inl{(
                wdl_truth_to_laws_truth(
                  Rules.move_to(kind,
                    Rules.State{wk, bk, pc, 0},
                    Rules.State{wk, bk, dest, 1}),
                  legal),
                wdl_truth_to_laws_truth(
                  U32.is_ne(
                    ClockedStep.white_piece.value(
                      kind, pc, dest,
                      Rules.State{wk, bk, dest, 1},
                      next, reset), 0),
                  yes))}
        case Inr{later}:
          Inr{Laws.finite_some_white_piece_matches_scan(
            rest, kind, wk, bk, pc, next,
            reset, later)}

def Laws.white_piece_scan_matches_finite_some(
  squares, kind, wk, bk, pc, next, reset,
  found):
  match squares:
    case Nil{}:
      match found:
    case +dest <> rest:
      match found:
        case Inl{head}:
          match head:
            case (legal, yes):
              Inl{(
                laws_truth_to_wdl_truth(
                  Rules.move_to(kind,
                    Rules.State{wk, bk, pc, 0},
                    Rules.State{wk, bk, dest, 1}),
                  legal),
                laws_truth_to_wdl_truth(
                  U32.is_ne(
                    ClockedStep.white_piece.value(
                      kind, pc, dest,
                      Rules.State{wk, bk, dest, 1},
                      next, reset), 0),
                  yes))}
        case Inr{later}:
          Inr{Laws.white_piece_scan_matches_finite_some(
            rest, kind, wk, bk, pc, next,
            reset, later)}

def finite_every_black_head_convert(
  +kind: U32, +wk: U32, +bk: U32,
  +pc: U32, +dest: U32,
  +next: ProofTree.Tree,
  pair: WDL.Truth(U32.is_ne(dest, pc)) &
    WDL.Truth(U32.is_ne(ProofTree.get_index(
      next, Rules.index(Rules.State{
        wk, dest, pc, 0})), 0))) ->
  Laws.Truth(Bool.not(U32.is_eq(dest, pc))) &
    Laws.Truth(U32.is_ne(ProofTree.get_index(
      next, Rules.index(Rules.State{
        wk, dest, pc, 0})), 0)):
  match pair:
    case (no_capture, positive):
      (wdl_truth_to_laws_truth(
        U32.is_ne(dest, pc), no_capture),
       wdl_truth_to_laws_truth(
        U32.is_ne(ProofTree.get_index(next,
          Rules.index(Rules.State{
            wk, dest, pc, 0})), 0),
        positive))

def Laws.finite_every_black_matches_scan(
  squares, kind, wk, bk, pc, next, all):
  match squares:
    case Nil{}:
      Unit{}
    case +dest <> rest:
      match all:
        case (head, tail):
          (legal =>
            finite_every_black_head_convert(
              kind, wk, bk, pc, dest, next,
              head(laws_truth_to_wdl_truth(
                Rules.black_move(kind, wk, bk,
                  pc, dest), legal))),
           Laws.finite_every_black_matches_scan(
             rest, kind, wk, bk, pc, next,
             tail))

def black_scan_head_to_finite(
  +wk: U32, +pc: U32, +dest: U32,
  +next: ProofTree.Tree,
  pair: Laws.Truth(Bool.not(U32.is_eq(dest,
    pc))) &
    Laws.Truth(U32.is_ne(ProofTree.get_index(
      next, Rules.index(Rules.State{
        wk, dest, pc, 0})), 0))) ->
  WDL.Truth(U32.is_ne(dest, pc)) &
    WDL.Truth(U32.is_ne(ProofTree.get_index(
      next, Rules.index(Rules.State{
        wk, dest, pc, 0})), 0)):
  match pair:
    case (no_capture, positive):
      (laws_truth_to_wdl_truth(
        U32.is_ne(dest, pc), no_capture),
       laws_truth_to_wdl_truth(
        U32.is_ne(ProofTree.get_index(next,
          Rules.index(Rules.State{
            wk, dest, pc, 0})), 0),
        positive))

def Laws.black_scan_matches_finite_every(
  squares, kind, wk, bk, pc, next, all):
  match squares:
    case Nil{}:
      Unit{}
    case +dest <> rest:
      match all:
        case (head, tail):
          (legal =>
            black_scan_head_to_finite(wk, pc, dest,
              next, head(wdl_truth_to_laws_truth(
                Rules.black_move(kind, wk, bk,
                  pc, dest), legal))),
           Laws.black_scan_matches_finite_every(
             rest, kind, wk, bk, pc, next,
             tail))

def Laws.finite_black_some_matches_legal_squares(
  squares, kind, wk, bk, pc, found):
  match squares:
    case Nil{}:
      match found:
    case dest <> rest:
      match found:
        case Inl{head}:
          Inl{wdl_truth_to_laws_truth(
            Rules.black_move(kind, wk, bk,
              pc, dest), head)}
        case Inr{later}:
          Inr{Laws.finite_black_some_matches_legal_squares(
            rest, kind, wk, bk, pc, later)}

def Laws.black_legal_squares_match_finite_some(
  squares, kind, wk, bk, pc, found):
  match squares:
    case Nil{}:
      match found:
    case dest <> rest:
      match found:
        case Inl{head}:
          Inl{laws_truth_to_wdl_truth(
            Rules.black_move(kind, wk, bk,
              pc, dest), head)}
        case Inr{later}:
          Inr{Laws.black_legal_squares_match_finite_some(
            rest, kind, wk, bk, pc, later)}

def Laws.minimax_has_move_has_witness(
  squares, kind, wk, bk, pc, yes):
  +new = Minimax.has_move(squares,
    kind, wk, bk, pc,
    False{})
  +old = Retro.black_has_move.squares(
    kind, wk, bk, pc,
    squares, False{})
  old_yes = equality_cast(Bool,
    Laws.Truth, new, old,
    Laws.minimax_has_move_matches_executable_scan(
      squares, kind, wk, bk,
      pc, False{}), yes)
  Laws.black_legal_squares_match_finite_some(
    squares, kind, wk, bk, pc,
    Laws.black_has_move_squares_sound(
      squares, kind, wk, bk, pc,
      old_yes))

def Laws.minimax_has_move_from_witness(
  squares, kind, wk, bk, pc,
  witness):
  +new = Minimax.has_move(squares,
    kind, wk, bk, pc,
    False{})
  +old = Retro.black_has_move.squares(
    kind, wk, bk, pc,
    squares, False{})
  old_yes = Laws.black_has_move_squares_complete(
    squares, kind, wk, bk, pc,
    False{},
    Laws.finite_black_some_matches_legal_squares(
      squares, kind, wk,
      bk, pc, witness))
  equality_cast(Bool,
    Laws.Truth, old, new,
    Equal.sym(Bool, new, old,
      Laws.minimax_has_move_matches_executable_scan(
        squares, kind, wk, bk,
        pc, False{})),
    old_yes)

def Laws.white_piece_squares_have_witness(
  squares, kind, wk, bk, pc, next, reset,
  found):
  match squares:
    case dest <> rest:
      match found:
        case Inl{head}:
          (dest, head)
        case Inr{later}:
          Laws.white_piece_squares_have_witness(
            rest, kind, wk, bk, pc, next,
            reset, later)
    case Nil{}:
      match found:

def clocked_step_white_king_scan_head(
  +kind: U32, +wk: U32, +bk: U32,
  +pc: U32, +dest: U32,
  +next: ProofTree.Tree,
  +head: Laws.Truth(Rules.move_to(kind,
    Rules.State{wk, bk, pc, 0},
    Rules.State{dest, bk, pc, 1}) &&
    U32.is_ne(ProofTree.get_index(next,
      Rules.index(Rules.State{dest, bk, pc, 1})),
      0))) ->
  Laws.Truth(Rules.move_to(kind,
    Rules.State{wk, bk, pc, 0},
    Rules.State{dest, bk, pc, 1})) &
  Laws.Truth(U32.is_ne(ProofTree.get_index(next,
    Rules.index(Rules.State{dest, bk, pc, 1})),
    0)):
  (and_left(Rules.move_to(kind,
      Rules.State{wk, bk, pc, 0},
      Rules.State{dest, bk, pc, 1}),
    U32.is_ne(ProofTree.get_index(next,
      Rules.index(Rules.State{dest, bk, pc, 1})),
      0), head),
   and_right(Rules.move_to(kind,
      Rules.State{wk, bk, pc, 0},
      Rules.State{dest, bk, pc, 1}),
    U32.is_ne(ProofTree.get_index(next,
      Rules.index(Rules.State{dest, bk, pc, 1})),
      0), head))

def Laws.clocked_step_white_king_scan_sound(
  squares, kind, wk, bk, pc, next, yes):
  match squares:
    case Nil{}:
      match yes:
    case +dest <> +rest:
      +move = Rules.move_to(kind,
        Rules.State{wk, bk, pc, 0},
        Rules.State{dest, bk, pc, 1})
      +positive = U32.is_ne(ProofTree.get_index(next,
        Rules.index(Rules.State{dest, bk, pc, 1})),
        0)
      +tail = ClockedStep.white_king.go(rest,
        kind, Rules.State{wk, bk, pc, 0},
        wk, bk, pc, next)
      or_cases(Laws.WhiteKingWinningSquares(
        dest <> rest, kind, wk, bk, pc, next),
        move && positive, tail, yes,
        head => Inl{clocked_step_white_king_scan_head(
          kind, wk, bk, pc, dest, next, head)},
        later => Inr{
          Laws.clocked_step_white_king_scan_sound(
            rest, kind, wk, bk, pc, next, later)})

def clocked_step_white_king_scan_complete_cons(
  +dest: U32, +rest: List<&2, U32>,
  +kind: U32, +wk: U32, +bk: U32,
  +pc: U32, +next: ProofTree.Tree,
  witness:
    (Laws.Truth(Rules.move_to(kind,
      Rules.State{wk, bk, pc, 0},
      Rules.State{dest, bk, pc, 1})) &
     Laws.Truth(U32.is_ne(ProofTree.get_index(next,
      Rules.index(Rules.State{dest, bk, pc, 1})),
      0))) |
    Laws.WhiteKingWinningSquares(rest, kind,
      wk, bk, pc, next),
  recurse: Laws.WhiteKingWinningSquares(rest,
    kind, wk, bk, pc, next) ->
    Laws.Truth(ClockedStep.white_king.go(
      rest, kind, Rules.State{wk, bk, pc, 0},
      wk, bk, pc, next))) ->
  Laws.Truth(ClockedStep.white_king.go(
    dest <> rest, kind,
    Rules.State{wk, bk, pc, 0}, wk, bk, pc,
    next)):
  match witness:
    case Inl{head}:
      match head:
        case (legal, yes):
          or_left(Rules.move_to(kind,
              Rules.State{wk, bk, pc, 0},
              Rules.State{dest, bk, pc, 1}) &&
              U32.is_ne(ProofTree.get_index(next,
                Rules.index(Rules.State{dest, bk, pc, 1})),
                0),
            ClockedStep.white_king.go(rest,
              kind, Rules.State{wk, bk, pc, 0},
              wk, bk, pc, next),
            and_intro(Rules.move_to(kind,
                Rules.State{wk, bk, pc, 0},
                Rules.State{dest, bk, pc, 1}),
              U32.is_ne(ProofTree.get_index(next,
                Rules.index(Rules.State{dest, bk, pc, 1})),
                0), legal,
              yes))
    case Inr{later}:
      or_right(Rules.move_to(kind,
          Rules.State{wk, bk, pc, 0},
          Rules.State{dest, bk, pc, 1}) &&
          U32.is_ne(ProofTree.get_index(next,
            Rules.index(Rules.State{dest, bk, pc, 1})),
            0),
        ClockedStep.white_king.go(rest,
          kind, Rules.State{wk, bk, pc, 0},
          wk, bk, pc, next),
        recurse(later))

def Laws.clocked_step_white_king_scan_complete(
  squares, kind, wk, bk, pc, next, witness):
  match squares:
    case Nil{}:
      match witness:
    case +dest <> +rest:
      clocked_step_white_king_scan_complete_cons(
        dest, rest, kind, wk, bk, pc, next,
        witness,
        later => Laws.clocked_step_white_king_scan_complete(
          rest, kind, wk, bk, pc, next, later))

def clocked_step_white_piece_scan_head(
  +kind: U32, +wk: U32, +bk: U32,
  +pc: U32, +dest: U32,
  +next: ProofTree.Tree, +reset: ProofTree.Tree,
  +head: Laws.Truth(Rules.move_to(kind,
    Rules.State{wk, bk, pc, 0},
    Rules.State{wk, bk, dest, 1}) &&
    U32.is_ne(ClockedStep.white_piece.value(
      kind, pc, dest,
      Rules.State{wk, bk, dest, 1},
      next, reset), 0))) ->
  Laws.Truth(Rules.move_to(kind,
    Rules.State{wk, bk, pc, 0},
    Rules.State{wk, bk, dest, 1})) &
  Laws.Truth(U32.is_ne(
    ClockedStep.white_piece.value(kind, pc,
      dest, Rules.State{wk, bk, dest, 1},
      next, reset), 0)):
  (and_left(Rules.move_to(kind,
      Rules.State{wk, bk, pc, 0},
      Rules.State{wk, bk, dest, 1}),
    U32.is_ne(ClockedStep.white_piece.value(
      kind, pc, dest,
      Rules.State{wk, bk, dest, 1},
      next, reset), 0), head),
   and_right(Rules.move_to(kind,
      Rules.State{wk, bk, pc, 0},
      Rules.State{wk, bk, dest, 1}),
    U32.is_ne(ClockedStep.white_piece.value(
      kind, pc, dest,
      Rules.State{wk, bk, dest, 1},
      next, reset), 0), head))

def Laws.clocked_step_white_piece_scan_sound(
  squares, kind, wk, bk, pc, next, reset, yes):
  match squares:
    case Nil{}:
      match yes:
    case +dest <> +rest:
      +move = Rules.move_to(kind,
        Rules.State{wk, bk, pc, 0},
        Rules.State{wk, bk, dest, 1})
      +positive = U32.is_ne(
        ClockedStep.white_piece.value(kind, pc,
          dest, Rules.State{wk, bk, dest, 1},
          next, reset), 0)
      +tail = ClockedStep.white_piece.go(rest,
        kind, Rules.State{wk, bk, pc, 0},
        wk, bk, pc, next, reset)
      or_cases(Laws.WhitePieceWinningSquares(
        dest <> rest, kind, wk, bk, pc,
        next, reset),
        move && positive, tail, yes,
        head => Inl{clocked_step_white_piece_scan_head(
          kind, wk, bk, pc, dest, next, reset,
          head)},
        later => Inr{
          Laws.clocked_step_white_piece_scan_sound(
            rest, kind, wk, bk, pc,
            next, reset, later)})

def clocked_step_white_piece_scan_complete_cons(
  +dest: U32, +rest: List<&2, U32>,
  +kind: U32, +wk: U32, +bk: U32,
  +pc: U32, +next: ProofTree.Tree,
  +reset: ProofTree.Tree,
  witness:
    (Laws.Truth(Rules.move_to(kind,
      Rules.State{wk, bk, pc, 0},
      Rules.State{wk, bk, dest, 1})) &
     Laws.Truth(U32.is_ne(
      ClockedStep.white_piece.value(kind, pc,
        dest, Rules.State{wk, bk, dest, 1},
        next, reset), 0))) |
    Laws.WhitePieceWinningSquares(rest, kind,
      wk, bk, pc, next, reset),
  recurse: Laws.WhitePieceWinningSquares(rest,
    kind, wk, bk, pc, next, reset) ->
    Laws.Truth(ClockedStep.white_piece.go(
      rest, kind, Rules.State{wk, bk, pc, 0},
      wk, bk, pc, next, reset))) ->
  Laws.Truth(ClockedStep.white_piece.go(
    dest <> rest, kind,
    Rules.State{wk, bk, pc, 0}, wk, bk, pc,
    next, reset)):
  match witness:
    case Inl{head}:
      match head:
        case (legal, yes):
          or_left(Rules.move_to(kind,
              Rules.State{wk, bk, pc, 0},
              Rules.State{wk, bk, dest, 1}) &&
              U32.is_ne(
                ClockedStep.white_piece.value(kind,
                  pc, dest,
                  Rules.State{wk, bk, dest, 1},
                  next, reset), 0),
            ClockedStep.white_piece.go(rest,
              kind, Rules.State{wk, bk, pc, 0},
              wk, bk, pc, next, reset),
            and_intro(Rules.move_to(kind,
                Rules.State{wk, bk, pc, 0},
                Rules.State{wk, bk, dest, 1}),
              U32.is_ne(
                ClockedStep.white_piece.value(kind,
                  pc, dest,
                  Rules.State{wk, bk, dest, 1},
                  next, reset), 0), legal,
              yes))
    case Inr{later}:
      or_right(Rules.move_to(kind,
          Rules.State{wk, bk, pc, 0},
          Rules.State{wk, bk, dest, 1}) &&
          U32.is_ne(
            ClockedStep.white_piece.value(kind,
              pc, dest,
              Rules.State{wk, bk, dest, 1},
              next, reset), 0),
        ClockedStep.white_piece.go(rest,
          kind, Rules.State{wk, bk, pc, 0},
          wk, bk, pc, next, reset),
        recurse(later))

def Laws.clocked_step_white_piece_scan_complete(
  squares, kind, wk, bk, pc, next, reset,
  witness):
  match squares:
    case Nil{}:
      match witness:
    case +dest <> +rest:
      clocked_step_white_piece_scan_complete_cons(
        dest, rest, kind, wk, bk, pc, next,
        reset, witness,
        later => Laws.clocked_step_white_piece_scan_complete(
          rest, kind, wk, bk, pc, next,
          reset, later))

def Laws.clocked_table_write_slot_reads_step(
  kind, clock, squares, next, reset,
  queen, rook, index, tree):
  Laws.proof_tree_index_read_after_write(
    tree, index,
    Bool.pick(U32, ClockedStep.value(kind,
      clock, Rules.decode(index), squares,
      next, reset, queen, rook), 1, 0))

def Laws.clocked_table_write_slot_preserves_full(
  kind, clock, squares, next, reset,
  queen, rook, index, tree, full):
  Laws.proof_tree_set_preserves_full(19n,
    tree, ProofTree.bits19(index),
    Bool.pick(U32, ClockedStep.value(kind,
      clock, Rules.decode(index), squares,
      next, reset, queen, rook), 1, 0),
    full)

def Laws.clocked_table_step_preserves_full(
  fuel, index, kind, clock, squares,
  next, reset, queen, rook, tree, full):
  match fuel:
    case 0n:
      full
    case 1n+rest:
      updated = Laws.clocked_table_write_slot_preserves_full(
        kind, clock, squares, next, reset,
        queen, rook, index, tree, full)
      Laws.clocked_table_step_preserves_full(
        rest, (index + 1 : U32), kind, clock,
        squares, next, reset, queen, rook,
        ClockedTables.write_slot(kind, clock,
          squares, next, reset, queen, rook,
          index, tree), updated)

def Laws.clocked_tabulate_reads_its_path(
  n, prefix, kind, clock, squares,
  next, reset, queen, rook, bits):
  match n bits:
    case 0n WNil{}:
      {==}
    case 1n++rest WCon{False{}, tail}:
      Laws.clocked_tabulate_reads_its_path(
        rest, prefix, kind, clock, squares,
        next, reset, queen, rook, tail)
    case 1n++rest WCon{True{}, tail}:
      Laws.clocked_tabulate_reads_its_path(
        rest, (prefix + U32.shln(1, rest) : U32),
        kind, clock, squares, next, reset,
        queen, rook, tail)

def Laws.clocked_tabulate_is_full(
  n, prefix, kind, clock, squares,
  next, reset, queen, rook):
  match n:
    case 0n:
      Unit{}
    case 1n++rest:
      (Laws.clocked_tabulate_is_full(
        rest, prefix, kind, clock, squares,
        next, reset, queen, rook),
       Laws.clocked_tabulate_is_full(
        rest, (prefix + U32.shln(1, rest) : U32),
        kind, clock, squares, next,
        reset, queen, rook))

def Laws.clocked_index_reverse_snoc(n, word, bit):
  match n word:
    case 0n WNil{}:
      {==}
    case 1n++rest WCon{head, tail}:
      Equal.cong(Word(1n+rest),
        Word(1n+(1n+rest)),
        suffix => ClockedIndex.snoc(1n+rest,
          suffix, head),
        ClockedIndex.reverse(1n+rest,
          ClockedIndex.snoc(rest, tail, bit)),
        WCon{bit, ClockedIndex.reverse(rest,
          tail)},
        Laws.clocked_index_reverse_snoc(
          rest, tail, bit))

def Laws.clocked_index_reverse_involution(n, word):
  match n word:
    case 0n WNil{}:
      {==}
    case 1n++rest WCon{head, tail}:
      Equal.trans(Word(1n+rest),
        ClockedIndex.reverse(1n+rest,
          ClockedIndex.snoc(rest,
            ClockedIndex.reverse(rest, tail),
            head)),
        WCon{head, ClockedIndex.reverse(rest,
          ClockedIndex.reverse(rest, tail))},
        WCon{head, tail},
        Laws.clocked_index_reverse_snoc(rest,
          ClockedIndex.reverse(rest, tail), head),
        Equal.cong(Word(rest), Word(1n+rest),
          suffix => WCon{head, suffix},
          ClockedIndex.reverse(rest,
            ClockedIndex.reverse(rest, tail)),
          tail,
          Laws.clocked_index_reverse_involution(
            rest, tail)))

def Laws.clocked_index_matches_existing_bits(index):
  match index:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, high}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.clocked_index_path_of_low_word(low):
  Equal.cong(Word(19n) & Word(13n),
    Word(19n),
    pair => ClockedIndex.reverse(19n,
      ClockedIndex.low19.fin(pair)),
    Encoding.split(13n, 19n,
      Encoding.append(13n, 19n, low,
        Word.zero(13n))),
    (low, Word.zero(13n)),
    Laws.word_split_append_inverse(19n, 13n,
      low, Word.zero(13n)))

def minimax_value_at_double_reverse(
  +fuel: Nat, +clock: Nat,
  +kind: U32,
  +squares: List<&2, U32>,
  +low: Word(19n)) ->
  {Minimax.value_at_path(fuel, clock,
    squares, kind,
    ClockedIndex.reverse(19n, low)) ==
    Bool.pick(U32, Minimax.value(fuel,
      clock, squares, kind,
      Rules.decode(U32{Encoding.append(
        13n, 19n, low,
        Word.zero(13n))})), 1, 0) : U32}:
  Equal.cong(Word(19n), U32,
    word => Bool.pick(U32,
      Minimax.value(fuel, clock, squares,
        kind,
        Rules.decode(U32{Encoding.append(
          13n, 19n, word,
          Word.zero(13n))})), 1, 0),
    ClockedIndex.reverse(19n,
      ClockedIndex.reverse(19n, low)),
    low,
    Laws.clocked_index_reverse_involution(
      19n, low))

def Laws.minimax_path_correct_canonical_index(
  paths, coverage, table, fuel, clock,
  kind, squares, cert, low):
  +index = {U32{Encoding.append(13n,
    19n, low, Word.zero(13n))} : U32}
  +bits = ProofTree.bits19(index)
  path_eq = Equal.trans(Word(19n),
    bits, ClockedIndex.path(index),
    ClockedIndex.reverse(19n, low),
    Laws.clocked_index_matches_existing_bits(
      index),
    Laws.clocked_index_path_of_low_word(low))
  first = Laws.minimax_path_correct_lookup(
    19n, fuel, clock, kind, squares,
    paths, table, cert, bits)
  second = Equal.cong(Word(19n), U32,
    path => Minimax.value_at_path(fuel,
      clock, squares, kind, path),
    PathTree.get(19n, Word(19n),
      paths, bits),
    ClockedIndex.reverse(19n, low),
    Equal.trans(Word(19n),
      PathTree.get(19n, Word(19n),
        paths, bits), bits,
      ClockedIndex.reverse(19n, low),
      coverage(bits), path_eq))
  third = minimax_value_at_double_reverse(
    fuel, clock, kind, squares, low)
  Equal.trans(U32,
    ProofTree.get_index(table, index),
    Minimax.value_at_path(fuel, clock,
      squares, kind,
      PathTree.get(19n, Word(19n),
        paths, bits)),
    Bool.pick(U32, Minimax.value(fuel,
      clock, squares, kind,
      Rules.decode(index)), 1, 0),
    first, Equal.trans(U32,
      Minimax.value_at_path(fuel, clock,
        squares, kind,
        PathTree.get(19n, Word(19n),
          paths, bits)),
      Minimax.value_at_path(fuel, clock,
        squares, kind,
        ClockedIndex.reverse(19n, low)),
      Bool.pick(U32, Minimax.value(fuel,
        clock, squares, kind,
        Rules.decode(index)), 1, 0),
      second, third))

def Laws.minimax_path_correct_valid_state(
  paths, coverage, table, fuel,
  clock, kind, squares, cert,
  state, valid):
  match state:
    case Rules.State{+wk, +bk, +pc, +side}:
      +source = {Rules.State{wk, bk, pc,
        side} : Rules.State}
      +index = Rules.index(source)
      +low = ClockedIndex.low19(index)
      +canonical = {U32{Encoding.append(
        13n, 19n, low,
        Word.zero(13n))} : U32}
      +index_eq =
        Laws.valid_state_index_is_canonical_low_word(
          kind, wk, bk, pc, side, valid)
      decoded = Equal.trans(Rules.State,
        Rules.decode(canonical),
        Rules.decode(index), source,
        Equal.cong(U32, Rules.State,
          value => Rules.decode(value),
          canonical, index,
          Equal.sym(U32, index,
            canonical, index_eq)),
        Laws.valid_state_index_roundtrip(
          kind, wk, bk, pc, side,
          valid))
      first = Equal.cong(U32, U32,
        value => ProofTree.get_index(
          table, value),
        index, canonical, index_eq)
      second =
        Laws.minimax_path_correct_canonical_index(
          paths, coverage, table,
          fuel, clock, kind, squares,
          cert, low)
      third = Equal.cong(Rules.State, U32,
        position => Bool.pick(U32,
          Minimax.value(fuel, clock,
            squares, kind, position),
          1, 0),
        Rules.decode(canonical),
        source, decoded)
      Equal.trans(U32,
        ProofTree.get_index(table, index),
        ProofTree.get_index(table,
          canonical),
        Bool.pick(U32,
          Minimax.value(fuel, clock,
            squares, kind, source),
          1, 0),
        first, Equal.trans(U32,
          ProofTree.get_index(table,
            canonical),
          Bool.pick(U32,
            Minimax.value(fuel, clock,
              squares, kind,
              Rules.decode(canonical)),
            1, 0),
          Bool.pick(U32,
            Minimax.value(fuel, clock,
              squares, kind, source),
            1, 0),
          second, third))

def Laws.minimax_path_correct_valid_state_bool(
  paths, coverage, table, fuel,
  clock, kind, squares, cert,
  state, valid):
  +value = Minimax.value(fuel, clock,
    squares, kind, state)
  Equal.trans(Bool,
    U32.is_ne(ProofTree.get_index(table,
      Rules.index(state)), 0),
    U32.is_ne(Bool.pick(U32, value,
      1, 0), 0),
    value,
    Equal.cong(U32, Bool,
      entry => U32.is_ne(entry, 0),
      ProofTree.get_index(table,
        Rules.index(state)),
      Bool.pick(U32, value, 1, 0),
      Laws.minimax_path_correct_valid_state(
        paths, coverage, table,
        fuel, clock, kind, squares,
        cert, state, valid)),
    bool_pick_ne_zero_is_bool(value))

def Laws.path_tree_prepend_lookup(depth, n, bit,
  tree, bits):
  match depth tree bits:
    case 0n PathTree.Leaf{word} WNil{}:
      {==}
    case 1n++rest PathTree.Leaf{word}
         WCon{head, tail}:
      {==}
    case 0n PathTree.Node{left, right} WNil{}:
      Laws.path_tree_prepend_lookup(
        0n, n, bit, left, WNil{})
    case 1n++rest PathTree.Node{left, right}
         WCon{False{}, tail}:
      Laws.path_tree_prepend_lookup(
        rest, n, bit, left, tail)
    case 1n++rest PathTree.Node{left, right}
         WCon{True{}, tail}:
      Laws.path_tree_prepend_lookup(
        rest, n, bit, right, tail)

def Laws.path_tree_drop_head_prepend(n, bit,
  tree):
  match tree:
    case PathTree.Leaf{word}:
      {==}
    case PathTree.Node{left, right}:
      +left_before = PathTree.drop_head(n,
        PathTree.prepend(n, bit, left))
      +right_before = PathTree.drop_head(n,
        PathTree.prepend(n, bit, right))
      Equal.trans(PathTree.Tree<Word(n)>,
        PathTree.Node{left_before,
          right_before},
        PathTree.Node{left,
          right_before},
        PathTree.Node{left, right},
        Equal.cong(PathTree.Tree<Word(n)>,
          PathTree.Tree<Word(n)>,
          branch => PathTree.Node{
            branch, right_before},
          left_before, left,
          Laws.path_tree_drop_head_prepend(
            n, bit, left)),
        Equal.cong(PathTree.Tree<Word(n)>,
          PathTree.Tree<Word(n)>,
          branch => PathTree.Node{
            left, branch},
          right_before, right,
          Laws.path_tree_drop_head_prepend(
            n, bit, right)))

def Laws.canonical_paths_have_coverage(n):
  match n:
    case 0n:
      {==}
    case 1n++rest:
      +children = PathTree.paths(rest)
      +left = PathTree.prepend(rest,
        False{}, children)
      +right = PathTree.prepend(rest,
        True{}, children)
      +left_drop = PathTree.drop_head(
        rest, left)
      +right_drop = PathTree.drop_head(
        rest, right)
      +child_cover =
        Laws.canonical_paths_have_coverage(
          rest)
      +left_drop_eq =
        Laws.path_tree_drop_head_prepend(
          rest, False{}, children)
      +right_drop_eq =
        Laws.path_tree_drop_head_prepend(
          rest, True{}, children)
      Laws.Both{
        Equal.cong(PathTree.Tree<Word(rest)>,
          PathTree.Tree<Word(1n+rest)>,
          branch => PathTree.prepend(
            rest, False{}, branch),
          children, left_drop,
          Equal.sym(PathTree.Tree<Word(rest)>,
            left_drop, children,
            left_drop_eq)),
        Laws.Both{
          equality_cast(
            PathTree.Tree<Word(rest)>,
            candidate =>
              Laws.CanonicalCoverage(rest,
                candidate),
            children, left_drop,
            Equal.sym(PathTree.Tree<Word(rest)>,
              left_drop, children,
              left_drop_eq),
            child_cover),
          Laws.Both{
            Equal.cong(
              PathTree.Tree<Word(rest)>,
              PathTree.Tree<Word(1n+rest)>,
              branch => PathTree.prepend(
                rest, True{}, branch),
              children, right_drop,
              Equal.sym(
                PathTree.Tree<Word(rest)>,
                right_drop, children,
                right_drop_eq)),
            equality_cast(
              PathTree.Tree<Word(rest)>,
              candidate =>
                Laws.CanonicalCoverage(rest,
                  candidate),
              children, right_drop,
              Equal.sym(PathTree.Tree<Word(rest)>,
                right_drop, children,
                right_drop_eq),
              child_cover)}}}

def Laws.canonical_coverage_lookup(n,
  tree, cover, bits):
  match n tree cover bits:
    case 0n PathTree.Leaf{word}
         proof WNil{}:
      proof
    case 0n PathTree.Node{left, right}
         impossible WNil{}:
      Empty.absurd(
        {PathTree.get(0n, Word(0n),
          PathTree.Node{left, right},
          WNil{}) == WNil{} : Word(0n)},
        impossible)
    case 1n++rest PathTree.Leaf{word}
         impossible WCon{bit, tail}:
      Empty.absurd(
        {PathTree.get(1n+rest,
          Word(1n+rest),
          PathTree.Leaf{word},
          WCon{bit, tail}) ==
          WCon{bit, tail} :
          Word(1n+rest)},
        impossible)
    case 1n++rest PathTree.Node{left, right}
         Laws.Both{left_eq,
           Laws.Both{left_cover,
             Laws.Both{right_eq,
               right_cover}}}
         WCon{False{}, tail}:
      +stripped = PathTree.drop_head(rest,
        left)
      +mid = PathTree.prepend(rest,
        False{}, stripped)
      +left_read = PathTree.get(rest,
        Word(1n+rest), left, tail)
      +mid_read = PathTree.get(rest,
        Word(1n+rest), mid, tail)
      +tail_read = PathTree.get(rest,
        Word(rest), stripped, tail)
      Equal.trans(Word(1n+rest),
        left_read, mid_read,
        WCon{False{}, tail},
        Equal.cong(
          PathTree.Tree<Word(1n+rest)>,
          Word(1n+rest),
          candidate => PathTree.get(rest,
            Word(1n+rest), candidate,
            tail),
          left, mid, left_eq),
        Equal.trans(Word(1n+rest),
          mid_read,
          WCon{False{}, tail_read},
          WCon{False{}, tail},
          Laws.path_tree_prepend_lookup(
            rest, rest, False{},
            stripped, tail),
          Equal.cong(Word(rest),
            Word(1n+rest),
            value => WCon{False{}, value},
            tail_read, tail,
            Laws.canonical_coverage_lookup(
              rest, stripped,
              left_cover, tail))))
    case 1n++rest PathTree.Node{left, right}
         Laws.Both{left_eq,
           Laws.Both{left_cover,
             Laws.Both{right_eq,
               right_cover}}}
         WCon{True{}, tail}:
      +stripped = PathTree.drop_head(rest,
        right)
      +mid = PathTree.prepend(rest,
        True{}, stripped)
      +right_read = PathTree.get(rest,
        Word(1n+rest), right, tail)
      +mid_read = PathTree.get(rest,
        Word(1n+rest), mid, tail)
      +tail_read = PathTree.get(rest,
        Word(rest), stripped, tail)
      Equal.trans(Word(1n+rest),
        right_read, mid_read,
        WCon{True{}, tail},
        Equal.cong(
          PathTree.Tree<Word(1n+rest)>,
          Word(1n+rest),
          candidate => PathTree.get(rest,
            Word(1n+rest), candidate,
            tail),
          right, mid, right_eq),
        Equal.trans(Word(1n+rest),
          mid_read,
          WCon{True{}, tail_read},
          WCon{True{}, tail},
          Laws.path_tree_prepend_lookup(
            rest, rest, True{},
            stripped, tail),
          Equal.cong(Word(rest),
            Word(1n+rest),
            value => WCon{True{}, value},
            tail_read, tail,
            Laws.canonical_coverage_lookup(
              rest, stripped,
              right_cover, tail))))

def exact_pawn_value_at_double_reverse(
  +pushes: Nat, +remaining: Nat,
  +squares: List<&2, U32>,
  +low: Word(19n)) ->
  {Exact.pawn_value_at_path(pushes,
    remaining, squares,
    ClockedIndex.reverse(19n, low)) ==
    Bool.pick(U32,
      Exact.value(pushes, remaining,
        squares, 4,
        Rules.decode(U32{Encoding.append(
          13n, 19n, low,
          Word.zero(13n))})),
      1, 0) : U32}:
  Equal.cong(Word(19n), U32,
    word => Bool.pick(U32,
      Exact.value(pushes, remaining,
        squares, 4,
        Rules.decode(U32{Encoding.append(
          13n, 19n, word,
          Word.zero(13n))})), 1, 0),
    ClockedIndex.reverse(19n,
      ClockedIndex.reverse(19n, low)),
    low,
    Laws.clocked_index_reverse_involution(
      19n, low))

def Laws.exact_pawn_path_correct_canonical_index(
  paths, cover, table, pushes,
  remaining, squares, cert, low):
  +index = {U32{Encoding.append(13n,
    19n, low, Word.zero(13n))} : U32}
  +bits = ProofTree.bits19(index)
  +lookup_path = PathTree.get(19n,
    Word(19n), paths, bits)
  path_eq = Equal.trans(Word(19n),
    lookup_path, bits,
    ClockedIndex.reverse(19n, low),
    Laws.canonical_coverage_lookup(
      19n, paths, cover, bits),
    Equal.trans(Word(19n),
      bits, ClockedIndex.path(index),
      ClockedIndex.reverse(19n, low),
      Laws.clocked_index_matches_existing_bits(
        index),
      Laws.clocked_index_path_of_low_word(
        low)))
  first = Laws.exact_pawn_path_correct_lookup(
    19n, pushes, remaining, squares,
    paths, table, cert, bits)
  second = Equal.cong(Word(19n), U32,
    path => Exact.pawn_value_at_path(
      pushes, remaining, squares, path),
    lookup_path,
    ClockedIndex.reverse(19n, low),
    path_eq)
  third = exact_pawn_value_at_double_reverse(
    pushes, remaining, squares, low)
  Equal.trans(U32,
    ProofTree.get_index(table, index),
    Exact.pawn_value_at_path(pushes,
      remaining, squares, lookup_path),
    Bool.pick(U32,
      Exact.value(pushes, remaining,
        squares, 4,
        Rules.decode(index)), 1, 0),
    first,
    Equal.trans(U32,
      Exact.pawn_value_at_path(pushes,
        remaining, squares, lookup_path),
      Exact.pawn_value_at_path(pushes,
        remaining, squares,
        ClockedIndex.reverse(19n, low)),
      Bool.pick(U32,
        Exact.value(pushes, remaining,
          squares, 4,
          Rules.decode(index)), 1, 0),
      second, third))

def Laws.exact_pawn_path_correct_valid_state(
  paths, cover, table, pushes,
  remaining, squares, cert,
  state, valid):
  match state:
    case Rules.State{+wk, +bk,
           +pc, +side}:
      +source = {Rules.State{wk,
        bk, pc, side} : Rules.State}
      +index = Rules.index(source)
      +low = ClockedIndex.low19(index)
      +canonical = {U32{
        Encoding.append(13n,
          19n, low,
          Word.zero(13n))} : U32}
      +value = Exact.value(pushes,
        remaining, squares, 4,
        source)
      +index_eq =
        Laws.valid_state_index_is_canonical_low_word(
          4, wk, bk, pc,
          side, valid)
      decoded = Equal.trans(
        Rules.State,
        Rules.decode(canonical),
        Rules.decode(index),
        source,
        Equal.cong(U32,
          Rules.State,
          candidate =>
            Rules.decode(candidate),
          canonical, index,
          Equal.sym(U32, index,
            canonical, index_eq)),
        Laws.valid_state_index_roundtrip(
          4, wk, bk, pc,
          side, valid))
      Equal.trans(U32,
        ProofTree.get_index(table,
          index),
        ProofTree.get_index(table,
          canonical),
        Bool.pick(U32, value,
          1, 0),
        Equal.cong(U32, U32,
          candidate =>
            ProofTree.get_index(
              table, candidate),
          index, canonical,
          index_eq),
        Equal.trans(U32,
          ProofTree.get_index(
            table, canonical),
          Bool.pick(U32,
            Exact.value(pushes,
              remaining,
              squares, 4,
              Rules.decode(
                canonical)),
            1, 0),
          Bool.pick(U32, value,
            1, 0),
          Laws.exact_pawn_path_correct_canonical_index(
            paths, cover,
            table, pushes,
            remaining, squares,
            cert, low),
          Equal.cong(Rules.State,
            U32,
            position => Bool.pick(
              U32,
              Exact.value(pushes,
                remaining,
                squares, 4,
                position),
              1, 0),
            Rules.decode(canonical),
            source, decoded)))

def Laws.exact_pawn_path_correct_valid_state_bool(
  paths, cover, table, pushes,
  remaining, squares, cert,
  state, valid):
  match state:
    case Rules.State{+wk, +bk, +pc, +side}:
      +source = {Rules.State{wk, bk,
        pc, side} : Rules.State}
      +index = Rules.index(source)
      +low = ClockedIndex.low19(index)
      +canonical = {U32{Encoding.append(
        13n, 19n, low,
        Word.zero(13n))} : U32}
      +value = Exact.value(pushes,
        remaining, squares, 4, source)
      +index_eq =
        Laws.valid_state_index_is_canonical_low_word(
          4, wk, bk, pc, side, valid)
      decoded = Equal.trans(Rules.State,
        Rules.decode(canonical),
        Rules.decode(index), source,
        Equal.cong(U32, Rules.State,
          candidate => Rules.decode(
            candidate),
          canonical, index,
          Equal.sym(U32, index,
            canonical, index_eq)),
        Laws.valid_state_index_roundtrip(
          4, wk, bk, pc, side,
          valid))
      read_eq = Equal.trans(U32,
        ProofTree.get_index(table, index),
        ProofTree.get_index(table,
          canonical),
        Bool.pick(U32, value, 1, 0),
        Equal.cong(U32, U32,
          candidate => ProofTree.get_index(
            table, candidate),
          index, canonical, index_eq),
        Equal.trans(U32,
          ProofTree.get_index(table,
            canonical),
          Bool.pick(U32,
            Exact.value(pushes,
              remaining, squares, 4,
              Rules.decode(canonical)),
            1, 0),
          Bool.pick(U32, value, 1, 0),
          Laws.exact_pawn_path_correct_canonical_index(
            paths, cover, table,
            pushes, remaining, squares,
            cert, low),
          Equal.cong(Rules.State, U32,
            position => Bool.pick(U32,
              Exact.value(pushes,
                remaining, squares, 4,
                position), 1, 0),
            Rules.decode(canonical),
            source, decoded)))
      Equal.trans(Bool,
        U32.is_ne(ProofTree.get_index(
          table, index), 0),
        U32.is_ne(Bool.pick(U32, value,
          1, 0), 0),
        value,
        Equal.cong(U32, Bool,
          entry => U32.is_ne(entry, 0),
          ProofTree.get_index(table,
            index),
          Bool.pick(U32, value, 1, 0),
          read_eq),
        bool_pick_ne_zero_is_bool(value))

def Laws.path_tree_lookup_is_path(n, bits):
  match n bits:
    case 0n WNil{}:
      {==}
    case 1n++rest WCon{False{}, +tail}:
      Equal.trans(Word(1n+rest),
        PathTree.get(rest, Word(1n+rest),
          PathTree.prepend(rest, False{},
            PathTree.paths(rest)), tail),
        WCon{False{}, PathTree.get(rest,
          Word(rest), PathTree.paths(rest),
          tail)},
        WCon{False{}, tail},
        Laws.path_tree_prepend_lookup(rest,
          rest, False{}, PathTree.paths(rest),
          tail),
        Equal.cong(Word(rest), Word(1n+rest),
          suffix => WCon{False{}, suffix},
          PathTree.get(rest, Word(rest),
            PathTree.paths(rest), tail),
          tail,
          Laws.path_tree_lookup_is_path(rest,
            tail)))

    case 1n++rest WCon{True{}, +tail}:
      Equal.trans(Word(1n+rest),
        PathTree.get(rest, Word(1n+rest),
          PathTree.prepend(rest, True{},
            PathTree.paths(rest)), tail),
        WCon{True{}, PathTree.get(rest,
          Word(rest), PathTree.paths(rest),
          tail)},
        WCon{True{}, tail},
        Laws.path_tree_prepend_lookup(rest,
          rest, True{}, PathTree.paths(rest),
          tail),
        Equal.cong(Word(rest), Word(1n+rest),
          suffix => WCon{True{}, suffix},
          PathTree.get(rest, Word(rest),
            PathTree.paths(rest), tail),
          tail,
          Laws.path_tree_lookup_is_path(rest,
            tail)))

def Laws.structural_path_tree_is_certified(n):
  (PathTree.paths(n),
    bits => Laws.path_tree_lookup_is_path(n,
      bits))

def Laws.canonical_path_tree_lookup(n, tree,
  same, bits):
  equality_cast(PathTree.Tree<Word(n)>,
    candidate =>
      {PathTree.get(n, Word(n), candidate,
        bits) == bits : Word(n)},
    PathTree.paths(n), tree,
    Equal.sym(PathTree.Tree<Word(n)>, tree,
      PathTree.paths(n), same),
    Laws.path_tree_lookup_is_path(n,
      bits))

def Laws.minimax_canonical_path_correct_valid_state_bool(
  paths, cover, table, fuel, clock,
  kind, squares, cert, state, valid):
  Laws.minimax_path_correct_valid_state_bool(
    paths,
    bits => Laws.canonical_coverage_lookup(
      19n, paths, cover, bits),
    table, fuel, clock, kind, squares,
    cert, state, valid)

def Laws.clocked_path_tabulation_lookup(
  depth, tree, kind, clock, squares,
  next, reset, queen, rook, bits):
  match depth tree bits:
    case 0n PathTree.Leaf{path} WNil{}:
      {==}
    case 1n+rest PathTree.Leaf{path}
         WCon{bit, tail}:
      {==}
    case 0n PathTree.Node{left, right} WNil{}:
      Laws.clocked_path_tabulation_lookup(
        0n, left, kind, clock, squares,
        next, reset, queen, rook, WNil{})
    case 1n+rest PathTree.Node{left, right}
         WCon{False{}, tail}:
      Laws.clocked_path_tabulation_lookup(
        rest, left, kind, clock, squares,
        next, reset, queen, rook, tail)
    case 1n+rest PathTree.Node{left, right}
         WCon{True{}, tail}:
      Laws.clocked_path_tabulation_lookup(
        rest, right, kind, clock, squares,
        next, reset, queen, rook, tail)

def Laws.clocked_tabulated_path_has_its_value(
  tree, kind, clock, squares, next, reset,
  queen, rook, bits, path):
  Equal.trans(U32,
    ProofTree.get(19n,
      ClockedTables.from_paths(tree, kind,
        clock, squares, next, reset,
        queen, rook), bits),
    ClockedTables.value_at_path(kind, clock,
      squares, next, reset, queen, rook,
      PathTree.get(19n, Word(19n),
        tree, bits)),
    ClockedTables.value_at_path(kind, clock,
      squares, next, reset, queen, rook,
      bits),
    Laws.clocked_path_tabulation_lookup(
      19n, tree, kind,
      clock, squares, next, reset,
      queen, rook, bits),
    Equal.cong(Word(19n), U32,
      path => ClockedTables.value_at_path(
        kind, clock, squares, next,
        reset, queen, rook, path),
      PathTree.get(19n, Word(19n),
        tree, bits),
      bits, path))

def clocked_value_at_double_reverse(
  +kind: U32, +clock: Nat,
  +squares: List<&2, U32>,
  +next: ProofTree.Tree, +reset: ProofTree.Tree,
  +queen: ProofTree.Tree, +rook: ProofTree.Tree,
  +low: Word(19n)) ->
  {ClockedTables.value_at_path(kind, clock,
    squares, next, reset, queen, rook,
    ClockedIndex.reverse(19n, low)) ==
    Bool.pick(U32, ClockedStep.value(kind,
      clock,
      Rules.decode(U32{Encoding.append(13n,
        19n, low, Word.zero(13n))}),
      squares, next, reset, queen, rook),
      1, 0) : U32}:
  Equal.cong(Word(19n), U32,
    word => Bool.pick(U32,
      ClockedStep.value(kind, clock,
        Rules.decode(U32{Encoding.append(
          13n, 19n, word,
          Word.zero(13n))}),
        squares, next, reset, queen,
        rook), 1, 0),
    ClockedIndex.reverse(19n,
      ClockedIndex.reverse(19n, low)),
    low,
    Laws.clocked_index_reverse_involution(
      19n, low))

def Laws.clocked_tabulation_reads_canonical_index(
  tree, coverage, kind, clock, squares,
  next, reset, queen, rook, low):
  +index = {U32{Encoding.append(13n, 19n,
    low, Word.zero(13n))} : U32}
  +bits = ProofTree.bits19(index)
  path_eq = Equal.trans(Word(19n),
    bits, ClockedIndex.path(index),
    ClockedIndex.reverse(19n, low),
    Laws.clocked_index_matches_existing_bits(
      index),
    Laws.clocked_index_path_of_low_word(low))
  first = Laws.clocked_tabulated_path_has_its_value(
    tree, kind, clock, squares, next, reset,
    queen, rook, bits, coverage(bits))
  second = Equal.cong(Word(19n), U32,
    path => ClockedTables.value_at_path(
      kind, clock, squares, next, reset,
      queen, rook, path),
    bits, ClockedIndex.reverse(19n, low),
    path_eq)
  third = clocked_value_at_double_reverse(
    kind, clock, squares, next, reset,
    queen, rook, low)
  Equal.trans(U32,
    ProofTree.get_index(
      ClockedTables.from_paths(tree, kind,
        clock, squares, next, reset,
        queen, rook), index),
    ClockedTables.value_at_path(kind, clock,
      squares, next, reset, queen, rook,
      bits),
    Bool.pick(U32, ClockedStep.value(kind,
      clock, Rules.decode(index), squares,
      next, reset, queen, rook), 1, 0),
    first,
    Equal.trans(U32,
      ClockedTables.value_at_path(kind, clock,
        squares, next, reset, queen, rook,
        bits),
      ClockedTables.value_at_path(kind, clock,
        squares, next, reset, queen, rook,
        ClockedIndex.reverse(19n, low)),
      Bool.pick(U32, ClockedStep.value(kind,
        clock, Rules.decode(index), squares,
        next, reset, queen, rook), 1, 0),
      second, third))

def Laws.nonpawn_base_reads_step(
  tree, coverage, kind, clock, squares,
  zero, low):
  Laws.clocked_tabulation_reads_canonical_index(
    tree, coverage, kind, clock, squares,
    zero, zero, zero, zero, low)

def Laws.nonpawn_step_reads_next(
  remaining, tree, coverage, kind,
  clock, squares, zero, low):
  Laws.clocked_tabulation_reads_canonical_index(
    tree, coverage, kind, clock, squares,
    ClockedTables.nonpawn.go(remaining,
      1n+clock, kind, squares, tree, zero),
    zero, zero, zero, low)

def Laws.clocked_step_at_hundred_white_is_draw(
  kind, wk, bk, pc, squares, next, reset,
  queen, rook):
  bool_and_false_right(
    Rules.valid(kind, Rules.State{wk, bk, pc, 0}) &&
    Bool.not(U32.is_eq(kind, 2)) &&
    Bool.not(U32.is_eq(kind, 3)))

def Laws.clocked_step_at_hundred_black_is_mate(
  kind, wk, bk, pc, squares, next, reset,
  queen, rook):
  Equal.cong(Bool, Bool,
    result =>
      Rules.valid(kind,
        Rules.State{wk, bk, pc, 1}) &&
      Bool.not(U32.is_eq(kind, 2)) &&
      Bool.not(U32.is_eq(kind, 3)) && result,
    ClockedStep.black_terminal(kind, wk,
      bk, pc, squares) || False{},
    ClockedStep.black_terminal(kind, wk,
      bk, pc, squares),
    bool_or_false_right(
      ClockedStep.black_terminal(kind, wk,
        bk, pc, squares)))

def Laws.minimax_zero_horizon_white_matches_clock100_step(
  kind, squares, wk, bk, pc, zero):
  Laws.clocked_step_at_hundred_white_is_draw(
    kind, wk, bk, pc, squares,
    zero, zero, zero, zero)

def Laws.minimax_zero_horizon_black_matches_clock100_step(
  kind, squares, wk, bk, pc, zero):
  +terminal = ClockedStep.black_terminal(
    kind, wk, bk, pc, squares)
  +middle = Rules.valid(kind,
    Rules.State{wk, bk, pc, 1}) &&
    Bool.not(U32.is_eq(kind, 2)) &&
    Bool.not(U32.is_eq(kind, 3)) &&
    terminal
  +prefix = Rules.valid(kind,
    Rules.State{wk, bk, pc, 1}) &&
    Bool.not(U32.is_eq(kind, 2)) &&
    Bool.not(U32.is_eq(kind, 3))
  +old_has = Retro.black_has_move.squares(
    kind, wk, bk, pc, squares, False{})
  +new_has = Minimax.has_move(squares,
    kind, wk, bk, pc, False{})
  +attack = Rules.attacks(kind, pc, bk, wk)
  Equal.trans(Bool,
    ClockedStep.value(kind, 100n,
      Rules.State{wk, bk, pc, 1},
      squares, zero, zero, zero, zero),
    middle,
    Minimax.value(0n, 100n, squares,
      kind, Rules.State{wk, bk, pc, 1}),
    Laws.clocked_step_at_hundred_black_is_mate(
      kind, wk, bk, pc, squares,
      zero, zero, zero, zero),
    Equal.trans(Bool,
      prefix && (Bool.not(old_has) &&
        attack),
      prefix && (Bool.not(new_has) &&
        attack),
      (prefix && Bool.not(new_has)) &&
        attack,
      Equal.cong(Bool, Bool,
        found => prefix &&
          (Bool.not(found) && attack),
        old_has, new_has,
        Equal.sym(Bool, new_has,
          old_has,
          Laws.minimax_has_move_matches_executable_scan(
            squares, kind, wk, bk, pc,
            False{}))),
      bool_and_assoc(prefix,
        Bool.not(new_has), attack)))

def Laws.minimax_zero_horizon_canonical_low(
  low, kind, squares, zero):
  match low:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}:
      +index = {U32{Encoding.append(13n,
        19n, low, Word.zero(13n))} : U32}
      Laws.minimax_zero_horizon_white_matches_clock100_step(
        kind, squares,
        U32.and(index, 63),
        U32.and(U32.shrn(index, 6n), 63),
        U32.and(U32.shrn(index, 12n), 63),
        zero)
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{True{}, WNil{}}}}}}}}}}}}}}}}}}}}:
      +index = {U32{Encoding.append(13n,
        19n, low, Word.zero(13n))} : U32}
      Laws.minimax_zero_horizon_black_matches_clock100_step(
        kind, squares,
        U32.and(index, 63),
        U32.and(U32.shrn(index, 6n), 63),
        U32.and(U32.shrn(index, 12n), 63),
        zero)

def Laws.minimax_nonpawn_base_certified(
  paths, kind, squares, zero):
  match paths:
    case PathTree.Leaf{path}:
      Equal.cong(Bool, U32,
        value => Bool.pick(U32, value, 1, 0),
        ClockedStep.value(kind, 100n,
          Rules.decode(Minimax.index_of_path(path)),
          squares, zero, zero, zero, zero),
        Minimax.value(0n, 100n, squares,
          kind,
          Rules.decode(Minimax.index_of_path(path))),
        Laws.minimax_zero_horizon_canonical_low(
          ClockedIndex.reverse(19n, path),
          kind, squares, zero))
    case PathTree.Node{left, right}:
      Laws.Both{
        Laws.minimax_nonpawn_base_certified(
          left, kind, squares, zero),
        Laws.minimax_nonpawn_base_certified(
          right, kind, squares, zero)}

def Laws.black_scan_legal_member(squares, kind, wk,
  bk, pc, dest, member, move):
  match squares:
    case Nil{}:
      match member:
    case head <> rest:
      match member:
        case Inl{equal}:
          Inl{equality_cast(U32,
            x => Laws.Truth(Rules.black_move(kind,
              wk, bk, pc, x)),
            dest, head, equal, move)}
        case Inr{later}:
          Inr{Laws.black_scan_legal_member(rest,
            kind, wk, bk, pc, dest, later, move)}

def Laws.black_scan_safe_member(squares, kind, wk,
  bk, pc, dest, won, member, safe, move):
  match squares:
    case Nil{}:
      match member:
    case head <> rest:
      match member:
        case Inl{+equal}:
          match safe:
            case (head_safe, tail_safe):
              head_move = equality_cast(U32,
                x => Laws.Truth(Rules.black_move(
                  kind, wk, bk, pc, x)),
                dest, head, equal, move)
              head_result = head_safe(head_move)
              equality_cast(U32,
                x => Laws.Truth(Bool.not(
                  U32.is_eq(x, pc))) &
                  Laws.Truth(U32.is_ne(
                    ProofTree.get_index(won,
                      Rules.index(Rules.State{
                        wk, x, pc, 0})), 0)),
                head, dest,
                Equal.sym(U32, dest, head, equal),
                head_result)
        case Inr{later}:
          match safe:
            case (head_safe, tail_safe):
              Laws.black_scan_safe_member(rest,
                kind, wk, bk, pc, dest, won,
                later, tail_safe, move)

def Laws.black_reply_consider_max_monotone(scan,
  rank, capture, legal):
  match scan:
    case Retro.BlackReplyScan{seen, all_won, maximum}:
      match legal:
        case False{}:
          Laws.u32_le_reflexive(maximum)
        case True{}:
          Laws.u32_max_upper_left(maximum, rank)

def Laws.black_reply_consider_max_covers_new(scan,
  rank, capture, legal, yes):
  match scan:
    case Retro.BlackReplyScan{seen, all_won, maximum}:
      match legal:
        case False{}:
          match yes:
        case True{}:
          Laws.u32_max_upper_right(maximum, rank)

def Laws.black_reply_square_scan_max_monotone(
  squares, kind, wk, bk, pc, won, scan):
  match squares:
    case Nil{}:
      Laws.u32_le_reflexive(
        Laws.BlackScanMaximum(scan))
    case +dest <> +rest:
      +rank = ProofTree.get_index(won,
        Rules.index(Rules.State{wk, dest, pc, 0}))
      +capture = U32.is_eq(dest, pc)
      +legal = Rules.black_move(kind, wk, bk, pc, dest)
      +next = Retro.black_reply_consider(scan,
        rank, capture, legal)
      Laws.u32_le_transitive(
        Laws.BlackScanMaximum(scan),
        Laws.BlackScanMaximum(next),
        Laws.BlackScanMaximum(
          Retro.black_reply_scan.squares(kind,
            wk, bk, pc, rest, won, next)),
        Laws.black_reply_consider_max_monotone(
          scan, rank, capture, legal),
        Laws.black_reply_square_scan_max_monotone(
          rest, kind, wk, bk, pc, won, next))

def Laws.black_reply_square_scan_max_bounds_legal(
  squares, kind, wk, bk, pc, won, scan):
  match squares:
    case Nil{}:
      Unit{}
    case +dest <> +rest:
      +rank = ProofTree.get_index(won,
        Rules.index(Rules.State{wk, dest, pc, 0}))
      +capture = U32.is_eq(dest, pc)
      +legal = Rules.black_move(kind, wk, bk, pc, dest)
      +next = Retro.black_reply_consider(scan,
        rank, capture, legal)
      +maximum = Laws.BlackScanMaximum(
        Retro.black_reply_scan.squares(kind,
          wk, bk, pc, rest, won, next))
      (move => Laws.u32_le_transitive(
          rank, Laws.BlackScanMaximum(next), maximum,
          Laws.black_reply_consider_max_covers_new(
            scan, rank, capture, legal, move),
          Laws.black_reply_square_scan_max_monotone(
            rest, kind, wk, bk, pc, won, next)),
       Laws.black_reply_square_scan_max_bounds_legal(
         rest, kind, wk, bk, pc, won, next))

def Laws.black_scan_bound_member(squares, kind, wk,
  bk, pc, dest, won, maximum, member, bound, move):
  match squares:
    case Nil{}:
      match member:
    case head <> rest:
      match member:
        case Inl{+equal}:
          match bound:
            case (head_bound, tail_bound):
              head_move = equality_cast(U32,
                x => Laws.Truth(Rules.black_move(
                  kind, wk, bk, pc, x)),
                dest, head, equal, move)
              result = head_bound(head_move)
              equality_cast(U32,
                x => Laws.Truth(U32.is_le(
                  ProofTree.get_index(won,
                    Rules.index(Rules.State{
                      wk, x, pc, 0})), maximum)),
                head, dest,
                Equal.sym(U32, dest, head, equal),
                result)
        case Inr{later}:
          match bound:
            case (head_bound, tail_bound):
              Laws.black_scan_bound_member(rest,
                kind, wk, bk, pc, dest, won,
                maximum, later, tail_bound, move)

def checked_and_separated(touch: Bool,
  separated: Laws.Truth(Bool.not(touch)),
  checked: Laws.Truth(touch)) -> Empty:
  match touch:
    case True{}:
      separated
    case False{}:
      checked

def Laws.lone_black_king_cannot_checkmate(kind, wk, bk, pc,
  turn, valid, checked):
  separated = Laws.legal_three_man_position_has_no_black_king_check(
    kind, wk, bk, pc, turn, valid)
  checked_and_separated(Position.kings_touch(wk, bk),
    separated, checked)

def white_mate_contradiction(+touch: Bool,
  separated: Laws.Truth(Bool.not(touch)),
  checked: WDL.Truth(touch)) -> Empty:
  match touch:
    case True{}:
      separated
    case False{}:
      checked

def Laws.white_mate_is_impossible(kind, wk, bk, pc, mate):
  match mate:
    case Tuple{valid, Tuple{checked, no_moves}}:
      separated = Laws.legal_three_man_position_has_no_black_king_check(
        kind, wk, bk, pc, 0,
        wdl_truth_to_laws_truth(
          Rules.valid(kind, Rules.State{wk, bk, pc, 0}), valid))
      white_mate_contradiction(Position.kings_touch(wk, bk),
        separated, checked)

def Laws.black_cannot_force_win(n, game, win):
  match n game:
    case 0n WDL.White{kind, wk, bk, pc}:
      Laws.white_mate_is_impossible(kind, wk, bk, pc, win)
    case 0n WDL.Black{kind, wk, bk, pc}:
      win
    case 0n WDL.KingsOnly{}:
      win
    case 0n WDL.BareBishop{}:
      win
    case 0n WDL.BareKnight{}:
      win
    case 1n+rest WDL.KingsOnly{}:
      win
    case 1n+rest WDL.BareBishop{}:
      win
    case 1n+rest WDL.BareKnight{}:
      win
    case 1n+rest WDL.Black{kind, wk, bk, pc}:
      match win:
        case Tuple{+next, Tuple{legal, child}}:
          Laws.black_cannot_force_win(rest, next, child)
    case 1n+rest WDL.White{kind, wk, bk, pc}:
      match win:
        case Inl{mate}:
          Laws.white_mate_is_impossible(kind, wk, bk, pc, mate)
        case Inr{pair}:
          match pair:
            case Tuple{has_move, replies}:
              match has_move:
                case Tuple{+next, legal}:
                  Laws.black_cannot_force_win(rest, next,
                    replies(next, legal))

def Laws.black_cannot_force_clocked_win(n, clock, game, win):
  match n game:
    case 0n WDL.White{kind, wk, bk, pc}:
      Laws.white_mate_is_impossible(kind, wk, bk, pc, win)
    case 0n WDL.Black{kind, wk, bk, pc}:
      win
    case 0n WDL.KingsOnly{}:
      win
    case 0n WDL.BareBishop{}:
      win
    case 0n WDL.BareKnight{}:
      win
    case 1n+rest WDL.KingsOnly{}:
      win
    case 1n+rest WDL.BareBishop{}:
      win
    case 1n+rest WDL.BareKnight{}:
      win
    case 1n+rest WDL.Black{kind, wk, bk, pc}:
      match win:
        case Tuple{clock_ok, Tuple{+next, Tuple{legal, child}}}:
          Laws.black_cannot_force_clocked_win(rest,
            Clocked.next_clock(clock,
              WDL.Black{kind, wk, bk, pc}, next), next, child)
    case 1n+rest WDL.White{kind, wk, bk, pc}:
      match win:
        case Inl{mate}:
          Laws.white_mate_is_impossible(kind, wk, bk, pc, mate)
        case Inr{pair}:
          match pair:
            case Tuple{clock_ok, Tuple{has_move, replies}}:
              match has_move:
                case Tuple{+next, legal}:
                  Laws.black_cannot_force_clocked_win(rest,
                    Clocked.next_clock(clock,
                      WDL.White{kind, wk, bk, pc}, next),
                    next, replies(next, legal))

def bishop_white_absurd(
  win: Clocked.ClockZeroWhiteWin(WDL.BareBishop{})) -> Empty:
  match win:
    case Tuple{plies, within}:
      match plies:
        case 0n:
          within
        case 1n+rest:
          within

def kings_white_absurd(
  win: Clocked.ClockZeroWhiteWin(WDL.KingsOnly{})) -> Empty:
  match win:
    case Tuple{plies, within}:
      match plies:
        case 0n:
          within
        case 1n+rest:
          within

def knight_white_absurd(
  win: Clocked.ClockZeroWhiteWin(WDL.BareKnight{})) -> Empty:
  match win:
    case Tuple{plies, within}:
      match plies:
        case 0n:
          within
        case 1n+rest:
          within

def dead_material_black_absurd(+game: WDL.Game,
  win: Clocked.ClockZeroBlackWin(game)) -> Empty:
  match win:
    case Tuple{plies, within}:
      Laws.black_cannot_force_clocked_win(plies, 0n,
        game, within)

def Laws.bare_kings_are_terminal_draw():
  (win => kings_white_absurd(win),
   black => dead_material_black_absurd(WDL.KingsOnly{}, black))

def Laws.bishop_material_is_terminal_draw(turn, wk, bk, pc):
  (win => bishop_white_absurd(win),
   black => dead_material_black_absurd(
    WDL.material_game(2, turn, wk, bk, pc), black))

def Laws.knight_material_is_terminal_draw(turn, wk, bk, pc):
  (win => knight_white_absurd(win),
   black => dead_material_black_absurd(
    WDL.material_game(3, turn, wk, bk, pc), black))

def Laws.bishop_zero_array_entry_is_correct(d, turn, wk, bk, pc):
  (Laws.uniform_array_get(d, 0,
     Rules.index(Rules.State{wk, bk, pc, turn})),
   Laws.bishop_material_is_terminal_draw(turn, wk, bk, pc))

def Laws.knight_zero_array_entry_is_correct(d, turn, wk, bk, pc):
  (Laws.uniform_array_get(d, 0,
     Rules.index(Rules.State{wk, bk, pc, turn})),
   Laws.knight_material_is_terminal_draw(turn, wk, bk, pc))

def first_of_four(+a: Bool, +b: Bool, +c: Bool, d: Bool,
  proof: Laws.Truth(a && b && c && d)) -> Laws.Truth(a):
  first = and_left(a && b && c, d, proof)
  second = and_left(a && b, c, first)
  and_left(a, b, second)

def second_of_four(+a: Bool, +b: Bool,
  +c: Bool, d: Bool,
  proof: Laws.Truth(a && b && c && d)) ->
  Laws.Truth(b):
  first = and_left(a && b && c, d, proof)
  second = and_left(a && b, c, first)
  and_right(a, b, second)

def pawn_single_push_strict_rank(
  +pc: U32, +dest: U32,
  +bound: Laws.Truth(U32.is_lt(pc, 64)),
  same: Laws.Truth(U32.is_eq(dest,
    U32.add(pc, 8)))) ->
  Laws.Truth(U32.is_lt(Rules.rank(pc),
    Rules.rank(dest))):
  +rank = Rules.rank(pc)
  increase = Laws.u32_inc_strict_below_max(
    rank, Laws.pawn_rank_below_max(
      pc, bound))
  pushed = equality_cast(U32,
    value => Laws.Truth(
      U32.is_lt(rank, value)),
    U32.inc(rank),
    Rules.rank(U32.add(pc, 8)),
    Equal.sym(U32,
      Rules.rank(U32.add(pc, 8)),
      U32.inc(rank),
      Laws.pawn_rank_after_single_push(
        pc, bound)),
    increase)
  target = Laws.u32_equality_reflects_identity(
    dest, U32.add(pc, 8), same)
  equality_cast(U32,
    value => Laws.Truth(U32.is_lt(
      rank, Rules.rank(value))),
    U32.add(pc, 8), dest,
    Equal.sym(U32, dest,
      U32.add(pc, 8), target),
    pushed)

def pawn_double_push_strict_rank(
  +pc: U32, +dest: U32,
  +bound: Laws.Truth(U32.is_lt(pc, 64)),
  first: Laws.Truth(U32.is_eq(
    Rules.rank(pc), 1)),
  same: Laws.Truth(U32.is_eq(dest,
    U32.add(pc, 16)))) ->
  Laws.Truth(U32.is_lt(Rules.rank(pc),
    Rules.rank(dest))):
  +rank = Rules.rank(pc)
  rank_is_one =
    Laws.u32_equality_reflects_identity(
      rank, 1, first)
  increase = equality_cast(U32,
    value => Laws.Truth(
      U32.is_lt(value,
        U32.add(value, 2))),
    1, rank,
    Equal.sym(U32, rank, 1,
      rank_is_one), Unit{})
  pushed = equality_cast(U32,
    value => Laws.Truth(
      U32.is_lt(rank, value)),
    U32.add(rank, 2),
    Rules.rank(U32.add(pc, 16)),
    Equal.sym(U32,
      Rules.rank(U32.add(pc, 16)),
      U32.add(rank, 2),
      Laws.pawn_rank_after_double_push(
        pc, bound)),
    increase)
  target = Laws.u32_equality_reflects_identity(
    dest, U32.add(pc, 16), same)
  equality_cast(U32,
    value => Laws.Truth(U32.is_lt(
      rank, Rules.rank(value))),
    U32.add(pc, 16), dest,
    Equal.sym(U32, dest,
      U32.add(pc, 16), target),
    pushed)

def Laws.pawn_step_increases_rank(
  pc, dest, wk, bk, bound, step):
  +single_a = U32.is_eq(dest,
    U32.add(pc, 8))
  +single_b = U32.is_ne(dest, wk)
  +single_c = U32.is_ne(dest, bk)
  +single_d = U32.is_lt(
    Rules.rank(dest), 7)
  +double_a = U32.is_eq(
    Rules.rank(pc), 1)
  +double_b = U32.is_eq(dest,
    U32.add(pc, 16))
  +double_c = U32.is_ne(
    U32.add(pc, 8), wk)
  +double_d = U32.is_ne(
    U32.add(pc, 8), bk)
  +double_e = U32.is_ne(dest, wk)
  +double_f = U32.is_ne(dest, bk)
  +single = single_a && single_b &&
    single_c && single_d
  +double = double_a && double_b &&
    double_c && double_d &&
    double_e && double_f
  or_cases(Laws.Truth(U32.is_lt(
      Rules.rank(pc), Rules.rank(dest))),
    single, double, step,
    first =>
      pawn_single_push_strict_rank(
        pc, dest, bound,
        first_of_four(single_a,
          single_b, single_c,
          single_d, first)),
    second =>
      +first5 = and_left(
        double_a && double_b &&
          double_c && double_d &&
          double_e,
        double_f, second)
      +first4 = and_left(
        double_a && double_b &&
          double_c && double_d,
        double_e, first5)
      pawn_double_push_strict_rank(
        pc, dest, bound,
        first_of_four(double_a,
          double_b, double_c,
          double_d, first4),
        second_of_four(double_a,
          double_b, double_c,
          double_d, first4)))

def bounds_from_placement(+a: Bool, +b: Bool,
  +wk_bound: Bool, +bk_bound: Bool, +pc_bound: Bool,
  +f: Bool, +g: Bool, h: Bool,
  placement: Laws.Truth(a && b && wk_bound && bk_bound &&
    pc_bound && f && g && h)) ->
  Laws.Truth(wk_bound) & Laws.Truth(bk_bound) &
    Laws.Truth(pc_bound):
  seven = and_left(a && b && wk_bound && bk_bound &&
    pc_bound && f && g, h, placement)
  six = and_left(a && b && wk_bound && bk_bound &&
    pc_bound && f, g, seven)
  +five = and_left(a && b && wk_bound && bk_bound &&
    pc_bound, f, six)
  pc_ok = and_right(a && b && wk_bound && bk_bound,
    pc_bound, five)
  +four = and_left(a && b && wk_bound && bk_bound,
    pc_bound, five)
  bk_ok = and_right(a && b && wk_bound, bk_bound, four)
  three = and_left(a && b && wk_bound, bk_bound, four)
  wk_ok = and_right(a && b, wk_bound, three)
  (wk_ok, (bk_ok, pc_ok))

def Laws.legal_state_squares_are_in_reverse_search_range(kind,
  s, valid):
  match s:
    case Rules.State{+wk, +bk, +pc, +turn}:
      placement = first_of_four(
        Rules.placement_valid(kind, wk, bk, pc, turn),
        Bool.not(Position.kings_touch(wk, bk)),
        Bool.not(U32.is_eq(kind, 4)) ||
          (U32.is_gt(Rules.rank(pc), 0) &&
            U32.is_lt(Rules.rank(pc), 7)),
        U32.is_eq(turn, 1) ||
          Bool.not(Rules.attacks(kind, pc, bk, wk)), valid)
      bounds_from_placement(
        U32.is_lt(kind, 5), U32.is_lt(turn, 2),
        U32.is_lt(wk, 64), U32.is_lt(bk, 64),
        U32.is_lt(pc, 64), U32.is_ne(wk, bk),
        U32.is_ne(wk, pc), U32.is_ne(bk, pc), placement)

def state_range_bk(+wk: U32, +bk: U32, +pc: U32,
  ranges: Laws.StateInRange(
    Rules.State{wk, bk, pc, 0})) ->
  Laws.Truth(U32.is_lt(bk, 64)):
  match ranges:
    case (wk_ok, (bk_ok, pc_ok)):
      bk_ok

def state_range_wk(+wk: U32, +bk: U32, +pc: U32,
  +turn: U32,
  ranges: Laws.StateInRange(
    Rules.State{wk, bk, pc, turn})) ->
  Laws.Truth(U32.is_lt(wk, 64)):
  match ranges:
    case (wk_ok, (bk_ok, pc_ok)):
      wk_ok

def state_range_pc(+wk: U32, +bk: U32, +pc: U32,
  +turn: U32,
  ranges: Laws.StateInRange(
    Rules.State{wk, bk, pc, turn})) ->
  Laws.Truth(U32.is_lt(pc, 64)):
  match ranges:
    case (wk_ok, (bk_ok, pc_ok)):
      pc_ok

def white_target_valid_from_move(
  +kind: U32, +wk: U32, +bk: U32,
  +pc: U32, +wk2: U32, +bk2: U32,
  +pc2: U32,
  legal: Laws.Truth(Rules.move_to(kind,
    Rules.State{wk, bk, pc, 0},
    Rules.State{wk2, bk2, pc2, 1}))) ->
  Laws.Truth(Rules.valid(kind,
    Rules.State{wk2, bk2, pc2, 1})):
  second_of_four(
    Rules.valid(kind, Rules.State{wk, bk, pc, 0}),
    Rules.valid(kind, Rules.State{wk2, bk2, pc2, 1}),
    U32.is_eq(bk, bk2),
    (U32.is_eq(pc, pc2) &&
      Rules.king_step(wk, wk2)) ||
    (U32.is_eq(wk, wk2) &&
      Rules.piece_step(kind, pc, pc2, wk, bk)),
    legal)

def black_noncapture_target_valid(
  +kind: U32, +wk: U32, +bk: U32,
  +pc: U32, +dest: U32,
  legal: Laws.Truth(Rules.black_move(
    kind, wk, bk, pc, dest)),
  no_capture: Laws.Truth(U32.is_ne(
    dest, pc))) ->
  Laws.Truth(Rules.valid(kind,
    Rules.State{wk, dest, pc, 0})):
  +step = Rules.king_step(bk, dest)
  +safe = Bool.not(Position.kings_touch(
    wk, dest))
  +capture = U32.is_eq(dest, pc)
  +valid = Rules.valid(kind,
    Rules.State{wk, dest, pc, 0})
  or_cases(Laws.Truth(valid), capture,
    valid,
    and_right(step && safe,
      capture || valid, legal),
    hit => Empty.absurd(
      Laws.Truth(valid),
      true_and_not_absurd(capture,
        hit, no_capture)),
    good => good)

def Laws.nonpawn_piece_value_is_next(
  kind, pc, dest, target, next,
  reset, no_pawn):
  +is_pawn = U32.is_eq(kind, 4)
  +read_reset = ProofTree.get_index(reset,
    Rules.index(target))
  +read_next = ProofTree.get_index(next,
    Rules.index(target))
  Equal.cong(Bool, U32,
    flag => Bool.pick(U32,
      flag && U32.is_ne(pc, dest),
      read_reset, read_next),
    is_pawn, False{},
    false_from_not_truth(is_pawn,
      no_pawn))

def Laws.nonpawn_piece_clock_increments(
  kind, pc, dest, clock, no_pawn):
  +is_pawn = U32.is_eq(kind, 4)
  Equal.cong(Bool, Nat,
    flag => Bool.pick(Nat,
      flag && U32.is_ne(pc, dest),
      0n, 1n+clock),
    is_pawn, False{},
    false_from_not_truth(is_pawn,
      no_pawn))

def Laws.minimax_king_scan_matches_step(
  fuel, clock, kind, wk, bk, pc,
  candidates, squares, paths,
  cover, next, cert):
  match candidates:
    case Nil{}:
      {==}
    case dest <> tail:
      +target = {Rules.State{dest, bk, pc,
        1} : Rules.State}
      +legal = Rules.move_to(kind,
        Rules.State{wk, bk, pc, 0},
        target)
      +left = U32.is_ne(
        ProofTree.get_index(next,
          Rules.index(target)), 0)
      +right = Minimax.value(fuel,
        1n+clock, squares, kind,
        target)
      +step_tail = ClockedStep.white_king.go(
        tail, kind,
        Rules.State{wk, bk, pc, 0},
        wk, bk, pc, next)
      +spec_tail = Minimax.win(1n+fuel,
        0n, tail, squares,
        Minimax.King{kind, wk, bk,
          pc, clock})
      guarded_or_cong(legal, left, right,
        step_tail, spec_tail,
        legal_proof =>
          Laws.minimax_canonical_path_correct_valid_state_bool(
            paths, cover, next, fuel,
            1n+clock, kind, squares,
            cert, target,
            white_target_valid_from_move(
              kind, wk, bk, pc,
              dest, bk, pc,
              legal_proof)),
        Laws.minimax_king_scan_matches_step(
          fuel, clock, kind, wk, bk, pc,
          tail, squares, paths, cover,
          next, cert))

def Laws.exact_pawn_king_scan_matches_step(
  push_rest, clock_rest, wk, bk, pc,
  candidates, squares, paths, cover,
  next, cert):
  match candidates:
    case Nil{}:
      {==}
    case dest <> tail:
      +target = {Rules.State{dest, bk, pc,
        1} : Rules.State}
      +legal = Rules.move_to(4,
        Rules.State{wk, bk, pc, 0},
        target)
      +left = U32.is_ne(
        ProofTree.get_index(next,
          Rules.index(target)), 0)
      +right = Exact.value(
        1n+push_rest, clock_rest,
        squares, 4, target)
      +step_tail = ClockedStep.white_king.go(
        tail, 4,
        Rules.State{wk, bk, pc, 0},
        wk, bk, pc, next)
      +spec_tail = Exact.win(
        1n+push_rest,
        1n+clock_rest, 0n,
        tail, squares,
        Exact.King{4, wk, bk, pc})
      guarded_or_cong(legal, left, right,
        step_tail, spec_tail,
        legal_proof =>
          Laws.exact_pawn_path_correct_valid_state_bool(
            paths, cover, next,
            1n+push_rest, clock_rest,
            squares, cert, target,
            white_target_valid_from_move(
              4, wk, bk, pc, dest,
              bk, pc, legal_proof)),
        Laws.exact_pawn_king_scan_matches_step(
          push_rest, clock_rest,
          wk, bk, pc, tail, squares,
          paths, cover, next, cert))

def exact_pawn_piece_head_matches(
  +flag: Bool, +push_rest: Nat,
  +clock_rest: Nat,
  +squares: List<&2, U32>,
  +paths: PathTree.Tree<Word(19n)>,
  +cover: Laws.CanonicalCoverage(19n,
    paths),
  +next: ProofTree.Tree,
  +reset: ProofTree.Tree,
  +next_cert: Laws.ExactPawnPathCorrect(
    1n+push_rest, clock_rest,
    squares, paths, next),
  +reset_cert: Laws.ExactPawnPathCorrect(
    push_rest, 100n,
    squares, paths, reset),
  +target: Rules.State,
  valid: Laws.Truth(Rules.valid(4,
    target))) ->
  {U32.is_ne(Bool.pick(U32, flag,
      ProofTree.get_index(reset,
        Rules.index(target)),
      ProofTree.get_index(next,
        Rules.index(target))), 0) ==
    Bool.pick(Bool, flag,
      Exact.value(push_rest, 100n,
        squares, 4, target),
      Exact.value(1n+push_rest,
        clock_rest, squares, 4,
        target)) : Bool}:
  match flag:
    case True{}:
      Laws.exact_pawn_path_correct_valid_state_bool(
        paths, cover, reset,
        push_rest, 100n, squares,
        reset_cert, target, valid)
    case False{}:
      Laws.exact_pawn_path_correct_valid_state_bool(
        paths, cover, next,
        1n+push_rest, clock_rest,
        squares, next_cert, target,
        valid)

def Laws.exact_pawn_piece_scan_matches_step(
  push_rest, clock_rest, wk, bk, pc,
  candidates, squares, paths, cover,
  next, reset, next_cert,
  reset_cert):
  match candidates:
    case Nil{}:
      {==}
    case dest <> tail:
      +target = {Rules.State{wk, bk,
        dest, 1} : Rules.State}
      +legal = Rules.move_to(4,
        Rules.State{wk, bk, pc, 0},
        target)
      +flag = U32.is_ne(pc, dest)
      +left = U32.is_ne(
        ClockedStep.white_piece.value(4,
          pc, dest, target, next,
          reset), 0)
      +right = Bool.pick(Bool, flag,
        Exact.value(push_rest, 100n,
          squares, 4, target),
        Exact.value(1n+push_rest,
          clock_rest, squares, 4,
          target))
      +step_tail = ClockedStep.white_piece.go(
        tail, 4,
        Rules.State{wk, bk, pc, 0},
        wk, bk, pc, next, reset)
      +spec_tail = Exact.win(
        1n+push_rest,
        1n+clock_rest, 0n, tail,
        squares,
        Exact.Piece{4, wk, bk, pc})
      guarded_or_cong(legal, left, right,
        step_tail, spec_tail,
        legal_proof =>
          exact_pawn_piece_head_matches(
            flag, push_rest,
            clock_rest, squares, paths,
            cover, next, reset,
            next_cert, reset_cert,
            target,
            white_target_valid_from_move(
              4, wk, bk, pc, wk, bk,
              dest, legal_proof)),
        Laws.exact_pawn_piece_scan_matches_step(
          push_rest, clock_rest,
          wk, bk, pc, tail, squares,
          paths, cover, next, reset,
          next_cert, reset_cert))

def Laws.exact_pawn_black_scan_all_matches_step(
  push_rest, clock_rest, wk, bk, pc,
  candidates, squares, paths, cover,
  next, cert, scan):
  match candidates:
    case Nil{}:
      {==}
    case dest <> tail:
      +target = {Rules.State{wk, dest, pc,
        0} : Rules.State}
      +legal = Rules.black_move(4,
        wk, bk, pc, dest)
      +capture = U32.is_eq(dest, pc)
      +rank = ProofTree.get_index(next,
        Rules.index(target))
      +child = Exact.value(1n+push_rest,
        clock_rest, squares, 4,
        target)
      +next_scan = Retro.black_reply_consider(
        scan, rank, capture, legal)
      +next_all = Laws.BlackScanAll(next_scan)
      +expected_all = Laws.BlackScanAll(scan) &&
        (Bool.not(legal) ||
          (Bool.not(capture) && child))
      +tail_value = Exact.win(1n+push_rest,
        1n+clock_rest, 0n, tail, squares,
        Exact.BlackAll{4, wk, bk,
          pc, next_all})
      +expected_value = Exact.win(1n+push_rest,
        1n+clock_rest, 0n, tail, squares,
        Exact.BlackAll{4, wk, bk,
          pc, expected_all})
      Equal.trans(Bool,
        Laws.BlackScanAll(
          Retro.black_reply_scan.squares(
            4, wk, bk, pc,
            candidates, next, scan)),
        tail_value, expected_value,
        Laws.exact_pawn_black_scan_all_matches_step(
          push_rest, clock_rest,
          wk, bk, pc, tail, squares,
          paths, cover, next, cert,
          next_scan),
        Equal.cong(Bool, Bool,
          all => Exact.win(1n+push_rest,
            1n+clock_rest, 0n,
            tail, squares,
            Exact.BlackAll{4, wk,
              bk, pc, all}),
          next_all, expected_all,
          black_all_head_cong(scan, rank,
            capture, legal, child,
            legal_proof =>
              no_capture =>
                Laws.exact_pawn_path_correct_valid_state_bool(
                  paths, cover, next,
                  1n+push_rest,
                  clock_rest, squares,
                  cert, target,
                  black_noncapture_target_valid(
                    4, wk, bk, pc,
                    dest, legal_proof,
                    no_capture)))))

def promotion_target_valid(+wk: U32,
  +bk: U32, +pc: U32, +kind: U32,
  proof: Laws.Truth(WDL.promotion(wk,
    bk, pc, kind, wk, bk,
    (pc + 8 : U32)))) ->
  Laws.Truth(Rules.valid(kind,
    Rules.State{wk, bk,
      (pc + 8 : U32), 1})):
  +target = (pc + 8 : U32)
  +prefix = Rules.pawn_can_promote(
    wk, bk, pc)
  +middle = U32.is_lt(kind, 4) &&
    U32.is_eq(wk, wk) &&
    U32.is_eq(bk, bk) &&
    U32.is_eq(target, target)
  inner = and_right(prefix,
    middle && Rules.valid(kind,
      Rules.State{wk, bk, target,
        1}), proof)
  and_right(middle,
    Rules.valid(kind,
      Rules.State{wk, bk, target,
        1}), inner)

def Laws.exact_pawn_promotion_matches_step(
  wk, bk, pc, squares, paths,
  cover, queen, rook, queen_cert,
  rook_cert):
  +target = {Rules.State{wk, bk,
    (pc + 8 : U32), 1} : Rules.State}
  +qguard = WDL.promotion(wk, bk,
    pc, 0, wk, bk, (pc + 8 : U32))
  +rguard = WDL.promotion(wk, bk,
    pc, 1, wk, bk, (pc + 8 : U32))
  +qread = U32.is_ne(
    ProofTree.get_index(queen,
      Rules.index(target)), 0)
  +rread = U32.is_ne(
    ProofTree.get_index(rook,
      Rules.index(target)), 0)
  +qvalue = Minimax.value(100n, 0n,
    squares, 0, target)
  +rvalue = Minimax.value(100n, 0n,
    squares, 1, target)
  +qeq = guarded_and_cong(qguard,
    qread, qvalue,
    yes =>
      Laws.minimax_canonical_path_correct_valid_state_bool(
        paths, cover, queen,
        100n, 0n, 0, squares,
        queen_cert, target,
        promotion_target_valid(wk,
          bk, pc, 0, yes)))
  +req = guarded_and_cong(rguard,
    rread, rvalue,
    yes =>
      Laws.minimax_canonical_path_correct_valid_state_bool(
        paths, cover, rook,
        100n, 0n, 1, squares,
        rook_cert, target,
        promotion_target_valid(wk,
          bk, pc, 1, yes)))
  Equal.trans(Bool,
    (qguard && qread) ||
      (rguard && rread),
    (qguard && qvalue) ||
      (rguard && rread),
    (qguard && qvalue) ||
      (rguard && rvalue),
    Equal.cong(Bool, Bool,
      q => q || (rguard && rread),
      qguard && qread,
      qguard && qvalue, qeq),
    Equal.cong(Bool, Bool,
      r => (qguard && qvalue) || r,
      rguard && rread,
      rguard && rvalue, req))

def Laws.exact_pawn_white_step_matches(
  push_rest, clock_rest, clock,
  wk, bk, pc, squares, paths,
  cover, next, reset, queen, rook,
  next_cert, reset_cert,
  queen_cert, rook_cert, budget):
  +before = Nat.is_lt(clock, 100n)
  +prefix = Rules.valid(4,
    Rules.State{wk, bk, pc, 0}) &&
    Bool.not(U32.is_eq(4, 2)) &&
    Bool.not(U32.is_eq(4, 3))
  +king_step = ClockedStep.white_king.go(
    squares, 4,
    Rules.State{wk, bk, pc, 0},
    wk, bk, pc, next)
  +piece_step = ClockedStep.white_piece.go(
    squares, 4,
    Rules.State{wk, bk, pc, 0},
    wk, bk, pc, next, reset)
  +promotion_step =
    ClockedStep.white_promotion(wk,
      bk, pc, queen, rook)
  +king_spec = Exact.win(1n+push_rest,
    1n+clock_rest, 0n,
    squares, squares,
    Exact.King{4, wk, bk, pc})
  +piece_spec = Exact.win(1n+push_rest,
    1n+clock_rest, 0n,
    squares, squares,
    Exact.Piece{4, wk, bk, pc})
  +promotion_spec =
    (WDL.promotion(wk, bk, pc, 0,
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
         (pc + 8 : U32), 1}))
  +white_step = (king_step ||
    piece_step) || promotion_step
  +white_spec = (king_spec ||
    piece_spec) || promotion_spec
  +king_eq = Laws.exact_pawn_king_scan_matches_step(
    push_rest, clock_rest, wk, bk,
    pc, squares, squares, paths,
    cover, next, next_cert)
  +piece_eq = Laws.exact_pawn_piece_scan_matches_step(
    push_rest, clock_rest, wk, bk,
    pc, squares, squares, paths,
    cover, next, reset,
    next_cert, reset_cert)
  +promotion_eq =
    Laws.exact_pawn_promotion_matches_step(
      wk, bk, pc, squares, paths,
      cover, queen, rook,
      queen_cert, rook_cert)
  +white_eq = Equal.trans(Bool,
    white_step,
    (king_spec || piece_spec) ||
      promotion_step,
    white_spec,
    Equal.trans(Bool,
      white_step,
      (king_spec || piece_step) ||
        promotion_step,
      (king_spec || piece_spec) ||
        promotion_step,
      Equal.cong(Bool, Bool,
        value => (value || piece_step) ||
          promotion_step,
        king_step, king_spec,
        king_eq),
      Equal.cong(Bool, Bool,
        value => (king_spec || value) ||
          promotion_step,
        piece_step, piece_spec,
        piece_eq)),
    Equal.cong(Bool, Bool,
      value =>
        (king_spec || piece_spec) ||
          value,
      promotion_step,
      promotion_spec,
      promotion_eq))
  Equal.trans(Bool,
    ClockedStep.value(4, clock,
      Rules.State{wk, bk, pc, 0},
      squares, next, reset,
      queen, rook),
    prefix && (before && white_spec),
    Exact.value(1n+push_rest,
      1n+clock_rest, squares, 4,
      Rules.State{wk, bk, pc, 0}),
    Equal.cong(Bool, Bool,
      inner => prefix &&
        (before && inner),
      white_step, white_spec,
      white_eq),
    drop_true_middle(prefix, before,
      white_spec,
      Laws.clock_budget_implies_before_hundred(
        clock, clock_rest,
        budget)))

def Laws.clocked_black_value_fin_unfold(
  kind, wk, bk, pc, scan):
  match scan:
    case Retro.BlackReplyScan{seen,
         all_won, maximum}:
      {==}

def Laws.exact_pawn_black_step_matches(
  push_rest, clock_rest, clock,
  wk, bk, pc, squares, paths,
  cover, next, reset, queen, rook,
  next_cert, budget):
  +initial = {Retro.BlackReplyScan{
    False{}, True{}, 0} :
    Retro.BlackReplyScan}
  +scan = Retro.black_reply_scan.squares(
    4, wk, bk, pc, squares,
    next, initial)
  +seen = Laws.BlackScanSeen(scan)
  +all = Laws.BlackScanAll(scan)
  +retro_has = Retro.black_has_move.squares(
    4, wk, bk, pc, squares,
    False{})
  +has = Minimax.has_move(squares,
    4, wk, bk, pc, False{})
  +spec_all = Exact.win(1n+push_rest,
    1n+clock_rest, 0n,
    squares, squares,
    Exact.BlackAll{4, wk, bk,
      pc, True{}})
  +before = Nat.is_lt(clock, 100n)
  +attack = Rules.attacks(4, pc,
    bk, wk)
  +prefix = Rules.valid(4,
    Rules.State{wk, bk, pc, 1}) &&
    Bool.not(U32.is_eq(4, 2)) &&
    Bool.not(U32.is_eq(4, 3))
  +step_body = ClockedStep.black_terminal(
    4, wk, bk, pc, squares) ||
    (before && ClockedStep.black_value.fin(
      4, wk, bk, pc, scan))
  +expanded =
    (Bool.not(retro_has) && attack) ||
    (before &&
      ((Bool.not(seen) && attack) ||
        (seen && all)))
  +before_spec =
    (Bool.not(has) && attack) ||
    ((before && has) && spec_all)
  +spec_body =
    (Bool.not(has) && attack) ||
    (has && spec_all)
  +seen_eq = Equal.trans(Bool,
    seen, retro_has, has,
    Laws.black_reply_scan_seen_matches_has_move(
      squares, 4, wk, bk, pc,
      next, initial),
    Equal.sym(Bool, has, retro_has,
      Laws.minimax_has_move_matches_executable_scan(
        squares, 4, wk, bk, pc,
        False{})))
  +all_eq =
    Laws.exact_pawn_black_scan_all_matches_step(
      push_rest, clock_rest,
      wk, bk, pc, squares,
      squares, paths, cover,
      next, next_cert, initial)
  +body_eq = Equal.trans(Bool,
    step_body, expanded, spec_body,
    Equal.cong(Bool, Bool,
      value =>
        ClockedStep.black_terminal(
          4, wk, bk, pc, squares) ||
        (before && value),
      ClockedStep.black_value.fin(
        4, wk, bk, pc, scan),
      (Bool.not(seen) && attack) ||
        (seen && all),
      Laws.clocked_black_value_fin_unfold(
        4, wk, bk, pc, scan)),
    Equal.trans(Bool,
      expanded, before_spec,
      spec_body,
      black_body_cong(before, attack,
        retro_has, seen, all, has,
        spec_all,
        Equal.sym(Bool, has,
          retro_has,
          Laws.minimax_has_move_matches_executable_scan(
            squares, 4, wk, bk,
            pc, False{})),
        seen_eq, all_eq),
      Equal.cong(Bool, Bool,
        value =>
          (Bool.not(has) && attack) ||
          ((value && has) &&
            spec_all),
        before, True{},
        truth_equals_true(before,
          Laws.clock_budget_implies_before_hundred(
            clock, clock_rest,
            budget)))))
  Equal.cong(Bool, Bool,
    body => prefix && body,
    step_body, spec_body,
    body_eq)

def Laws.exact_pawn_step_canonical_low(
  low, push_rest, clock_rest,
  clock, squares, paths, cover,
  next, reset, queen, rook,
  next_cert, reset_cert,
  queen_cert, rook_cert, budget):
  match low:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}:
      +index = {U32{Encoding.append(13n,
        19n, low, Word.zero(13n))} : U32}
      Laws.exact_pawn_white_step_matches(
        push_rest, clock_rest,
        clock, U32.and(index, 63),
        U32.and(U32.shrn(index, 6n),
          63),
        U32.and(U32.shrn(index, 12n),
          63),
        squares, paths, cover,
        next, reset, queen, rook,
        next_cert, reset_cert,
        queen_cert, rook_cert, budget)
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{True{}, WNil{}}}}}}}}}}}}}}}}}}}}:
      +index = {U32{Encoding.append(13n,
        19n, low, Word.zero(13n))} : U32}
      Laws.exact_pawn_black_step_matches(
        push_rest, clock_rest,
        clock, U32.and(index, 63),
        U32.and(U32.shrn(index, 6n),
          63),
        U32.and(U32.shrn(index, 12n),
          63),
        squares, paths, cover,
        next, reset, queen, rook,
        next_cert, budget)

def Laws.exact_pawn_layer_certified(
  subpaths, paths, cover,
  push_rest, clock_rest, clock,
  squares, next, reset, queen,
  rook, next_cert, reset_cert,
  queen_cert, rook_cert, budget):
  match subpaths:
    case PathTree.Leaf{path}:
      Equal.cong(Bool, U32,
        value => Bool.pick(U32, value,
          1, 0),
        ClockedStep.value(4, clock,
          Rules.decode(
            Minimax.index_of_path(path)),
          squares, next, reset,
          queen, rook),
        Exact.value(1n+push_rest,
          1n+clock_rest, squares, 4,
          Rules.decode(
            Minimax.index_of_path(path))),
        Laws.exact_pawn_step_canonical_low(
          ClockedIndex.reverse(19n,
            path), push_rest,
          clock_rest, clock, squares,
          paths, cover, next, reset,
          queen, rook, next_cert,
          reset_cert, queen_cert,
          rook_cert, budget))
    case PathTree.Node{left, right}:
      Laws.Both{
        Laws.exact_pawn_layer_certified(
          left, paths, cover,
          push_rest, clock_rest,
          clock, squares, next,
          reset, queen, rook,
          next_cert, reset_cert,
          queen_cert, rook_cert,
          budget),
        Laws.exact_pawn_layer_certified(
          right, paths, cover,
          push_rest, clock_rest,
          clock, squares, next,
          reset, queen, rook,
          next_cert, reset_cert,
          queen_cert, rook_cert,
          budget)}

def Laws.minimax_nonpawn_piece_scan_matches_step(
  fuel, clock, kind, wk, bk, pc,
  candidates, squares, paths, cover,
  next, reset, cert, no_pawn):
  match candidates:
    case Nil{}:
      {==}
    case dest <> tail:
      +target = {Rules.State{wk, bk, dest,
        1} : Rules.State}
      +legal = Rules.move_to(kind,
        Rules.State{wk, bk, pc, 0},
        target)
      +picked_clock = Bool.pick(Nat,
        U32.is_eq(kind, 4) &&
          U32.is_ne(pc, dest),
        0n, 1n+clock)
      +left = U32.is_ne(
        ClockedStep.white_piece.value(kind,
          pc, dest, target, next, reset),
        0)
      +right = Minimax.value(fuel,
        picked_clock, squares, kind,
        target)
      +step_tail = ClockedStep.white_piece.go(
        tail, kind,
        Rules.State{wk, bk, pc, 0},
        wk, bk, pc, next, reset)
      +spec_tail = Minimax.win(1n+fuel,
        0n, tail, squares,
        Minimax.Piece{kind, wk, bk,
          pc, clock})
      guarded_or_cong(legal, left, right,
        step_tail, spec_tail,
        legal_proof =>
          +valid = white_target_valid_from_move(
            kind, wk, bk, pc, wk, bk,
            dest, legal_proof)
          +read = ProofTree.get_index(next,
            Rules.index(target))
          +actual = Minimax.value(fuel,
            1n+clock, squares, kind,
            target)
          Equal.trans(Bool, left,
            U32.is_ne(read, 0), right,
            Equal.cong(U32, Bool,
              value => U32.is_ne(value, 0),
              ClockedStep.white_piece.value(
                kind, pc, dest, target,
                next, reset), read,
              Laws.nonpawn_piece_value_is_next(
                kind, pc, dest, target,
                next, reset, no_pawn)),
            Equal.trans(Bool,
              U32.is_ne(read, 0),
              actual, right,
              Laws.minimax_canonical_path_correct_valid_state_bool(
                paths, cover, next, fuel,
                1n+clock, kind, squares,
                cert, target, valid),
              Equal.sym(Bool, right, actual,
                Equal.cong(Nat, Bool,
                  current => Minimax.value(
                    fuel, current,
                    squares, kind, target),
                  picked_clock, 1n+clock,
                  Laws.nonpawn_piece_clock_increments(
                    kind, pc, dest,
                    clock, no_pawn))))),
        Laws.minimax_nonpawn_piece_scan_matches_step(
          fuel, clock, kind, wk, bk,
          pc, tail, squares, paths,
          cover, next, reset, cert,
          no_pawn))

def Laws.minimax_nonpawn_white_step_matches(
  fuel, clock, kind, wk, bk, pc,
  squares, paths, cover, next,
  zero, cert, no_pawn):
  +before = Nat.is_lt(clock, 100n)
  +prefix = Rules.valid(kind,
    Rules.State{wk, bk, pc, 0}) &&
    Bool.not(U32.is_eq(kind, 2)) &&
    Bool.not(U32.is_eq(kind, 3))
  +king_step = ClockedStep.white_king.go(
    squares, kind,
    Rules.State{wk, bk, pc, 0},
    wk, bk, pc, next)
  +piece_step = ClockedStep.white_piece.go(
    squares, kind,
    Rules.State{wk, bk, pc, 0},
    wk, bk, pc, next, zero)
  +king_spec = Minimax.win(1n+fuel,
    0n, squares, squares,
    Minimax.King{kind, wk, bk,
      pc, clock})
  +piece_spec = Minimax.win(1n+fuel,
    0n, squares, squares,
    Minimax.Piece{kind, wk, bk,
      pc, clock})
  +promotion_step =
    ClockedStep.white_promotion(wk, bk,
      pc, zero, zero)
  +promotion_spec =
    (WDL.promotion(wk, bk, pc, 0,
       wk, bk, (pc + 8 : U32)) &&
     Minimax.value(fuel, 0n, squares,
       0, Rules.State{wk, bk,
         (pc + 8 : U32), 1})) ||
    (WDL.promotion(wk, bk, pc, 1,
       wk, bk, (pc + 8 : U32)) &&
     Minimax.value(fuel, 0n, squares,
       1, Rules.State{wk, bk,
         (pc + 8 : U32), 1}))
  +white_step = (king_step || piece_step) ||
    (U32.is_eq(kind, 4) &&
      promotion_step)
  +white_spec = (king_spec || piece_spec) ||
    (U32.is_eq(kind, 4) &&
      promotion_spec)
  white_eq = white_or_cong_without_pawn(
    U32.is_eq(kind, 4), king_step,
    king_spec, piece_step, piece_spec,
    promotion_step, promotion_spec,
    no_pawn,
    Laws.minimax_king_scan_matches_step(
      fuel, clock, kind, wk, bk, pc,
      squares, squares, paths,
      cover, next, cert),
    Laws.minimax_nonpawn_piece_scan_matches_step(
      fuel, clock, kind, wk, bk, pc,
      squares, squares, paths, cover,
      next, zero, cert, no_pawn))
  Equal.trans(Bool,
    ClockedStep.value(kind, clock,
      Rules.State{wk, bk, pc, 0},
      squares, next, zero,
      zero, zero),
    prefix && (before && white_spec),
    Minimax.value(1n+fuel, clock,
      squares, kind,
      Rules.State{wk, bk, pc, 0}),
    Equal.cong(Bool, Bool,
      inner => prefix &&
        (before && inner),
      white_step, white_spec,
      white_eq),
    bool_and_assoc(prefix, before,
      white_spec))

def Laws.minimax_black_scan_all_matches_step(
  fuel, clock, kind, wk, bk, pc,
  candidates, squares, paths, cover,
  next, cert, scan):
  match candidates:
    case Nil{}:
      {==}
    case dest <> tail:
      +target = {Rules.State{wk, dest, pc,
        0} : Rules.State}
      +legal = Rules.black_move(kind,
        wk, bk, pc, dest)
      +capture = U32.is_eq(dest, pc)
      +rank = ProofTree.get_index(next,
        Rules.index(target))
      +child = Minimax.value(fuel,
        1n+clock, squares, kind,
        target)
      +next_scan = Retro.black_reply_consider(
        scan, rank, capture, legal)
      +next_all = Laws.BlackScanAll(next_scan)
      +expected_all = Laws.BlackScanAll(scan) &&
        (Bool.not(legal) ||
          (Bool.not(capture) && child))
      +tail_value = Minimax.win(1n+fuel,
        0n, tail, squares,
        Minimax.BlackAll{kind, wk, bk,
          pc, clock, next_all})
      +expected_value = Minimax.win(1n+fuel,
        0n, tail, squares,
        Minimax.BlackAll{kind, wk, bk,
          pc, clock, expected_all})
      Equal.trans(Bool,
        Laws.BlackScanAll(
          Retro.black_reply_scan.squares(
            kind, wk, bk, pc,
            candidates, next, scan)),
        tail_value, expected_value,
        Laws.minimax_black_scan_all_matches_step(
          fuel, clock, kind, wk, bk,
          pc, tail, squares, paths,
          cover, next, cert, next_scan),
        Equal.cong(Bool, Bool,
          all => Minimax.win(1n+fuel,
            0n, tail, squares,
            Minimax.BlackAll{kind, wk,
              bk, pc, clock, all}),
          next_all, expected_all,
          black_all_head_cong(scan, rank,
            capture, legal, child,
            legal_proof =>
              no_capture =>
                Laws.minimax_canonical_path_correct_valid_state_bool(
                  paths, cover, next,
                  fuel, 1n+clock, kind,
                  squares, cert, target,
                  black_noncapture_target_valid(
                    kind, wk, bk, pc,
                    dest, legal_proof,
                    no_capture)))))

def Laws.minimax_nonpawn_black_step_matches(
  fuel, clock, kind, wk, bk, pc,
  squares, paths, cover, next,
  zero, cert):
  +initial = {Retro.BlackReplyScan{
    False{}, True{}, 0} :
    Retro.BlackReplyScan}
  +scan = Retro.black_reply_scan.squares(
    kind, wk, bk, pc, squares,
    next, initial)
  +seen = Laws.BlackScanSeen(scan)
  +all = Laws.BlackScanAll(scan)
  +retro_has = Retro.black_has_move.squares(
    kind, wk, bk, pc, squares,
    False{})
  +has = Minimax.has_move(squares,
    kind, wk, bk, pc, False{})
  +spec_all = Minimax.win(1n+fuel,
    0n, squares, squares,
    Minimax.BlackAll{kind, wk, bk,
      pc, clock, True{}})
  +before = Nat.is_lt(clock, 100n)
  +attack = Rules.attacks(kind, pc,
    bk, wk)
  +prefix = Rules.valid(kind,
    Rules.State{wk, bk, pc, 1}) &&
    Bool.not(U32.is_eq(kind, 2)) &&
    Bool.not(U32.is_eq(kind, 3))
  +step_body = ClockedStep.black_terminal(
    kind, wk, bk, pc, squares) ||
    (before && ClockedStep.black_value.fin(
      kind, wk, bk, pc, scan))
  +expanded =
    (Bool.not(retro_has) && attack) ||
    (before &&
      ((Bool.not(seen) && attack) ||
        (seen && all)))
  +spec_body =
    (Bool.not(has) && attack) ||
    ((before && has) && spec_all)
  +seen_eq = Equal.trans(Bool,
    seen, retro_has, has,
    Laws.black_reply_scan_seen_matches_has_move(
      squares, kind, wk, bk, pc,
      next, initial),
    Equal.sym(Bool, has, retro_has,
      Laws.minimax_has_move_matches_executable_scan(
        squares, kind, wk, bk, pc,
        False{})))
  +all_eq =
    Laws.minimax_black_scan_all_matches_step(
      fuel, clock, kind, wk, bk, pc,
      squares, squares, paths, cover,
      next, cert, initial)
  +body_eq = Equal.trans(Bool,
    step_body, expanded, spec_body,
    Equal.cong(Bool, Bool,
      value =>
        ClockedStep.black_terminal(kind,
          wk, bk, pc, squares) ||
        (before && value),
      ClockedStep.black_value.fin(kind,
        wk, bk, pc, scan),
      (Bool.not(seen) && attack) ||
        (seen && all),
      Laws.clocked_black_value_fin_unfold(
        kind, wk, bk, pc, scan)),
    black_body_cong(before, attack,
      retro_has, seen, all, has,
      spec_all,
      Equal.sym(Bool, has, retro_has,
        Laws.minimax_has_move_matches_executable_scan(
          squares, kind, wk, bk, pc,
          False{})),
      seen_eq, all_eq))
  Equal.cong(Bool, Bool,
    body => prefix && body,
    step_body, spec_body, body_eq)

def Laws.minimax_nonpawn_step_canonical_low(
  low, fuel, clock, kind, squares,
  paths, cover, next, zero, cert,
  no_pawn):
  match low:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}:
      +index = {U32{Encoding.append(13n,
        19n, low, Word.zero(13n))} : U32}
      Laws.minimax_nonpawn_white_step_matches(
        fuel, clock, kind,
        U32.and(index, 63),
        U32.and(U32.shrn(index, 6n), 63),
        U32.and(U32.shrn(index, 12n), 63),
        squares, paths, cover, next,
        zero, cert, no_pawn)
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{True{}, WNil{}}}}}}}}}}}}}}}}}}}}:
      +index = {U32{Encoding.append(13n,
        19n, low, Word.zero(13n))} : U32}
      Laws.minimax_nonpawn_black_step_matches(
        fuel, clock, kind,
        U32.and(index, 63),
        U32.and(U32.shrn(index, 6n), 63),
        U32.and(U32.shrn(index, 12n), 63),
        squares, paths, cover, next,
        zero, cert)

def Laws.minimax_nonpawn_layer_certified(
  subpaths, paths, cover, fuel,
  clock, kind, squares, next,
  zero, cert, no_pawn):
  match subpaths:
    case PathTree.Leaf{path}:
      Equal.cong(Bool, U32,
        value => Bool.pick(U32, value, 1, 0),
        ClockedStep.value(kind, clock,
          Rules.decode(Minimax.index_of_path(path)),
          squares, next, zero,
          zero, zero),
        Minimax.value(1n+fuel, clock,
          squares, kind,
          Rules.decode(Minimax.index_of_path(path))),
        Laws.minimax_nonpawn_step_canonical_low(
          ClockedIndex.reverse(19n, path),
          fuel, clock, kind, squares,
          paths, cover, next, zero,
          cert, no_pawn))
    case PathTree.Node{left, right}:
      Laws.Both{
        Laws.minimax_nonpawn_layer_certified(
          left, paths, cover, fuel,
          clock, kind, squares, next,
          zero, cert, no_pawn),
        Laws.minimax_nonpawn_layer_certified(
          right, paths, cover, fuel,
          clock, kind, squares, next,
          zero, cert, no_pawn)}

def Laws.minimax_nonpawn_go_certified(
  remaining, clock, kind, squares,
  paths, cover, zero, no_pawn,
  budget):
  match remaining:
    case 0n:
      clock_eq = Equal.trans(Nat,
        clock, Nat.add(clock, 0n),
        100n,
        Equal.sym(Nat,
          Nat.add(clock, 0n), clock,
          Laws.nat_add_right_zero(clock)),
        budget)
      equality_cast(Nat,
        current =>
          Laws.MinimaxPathCorrect(0n,
            current, kind, squares,
            paths,
            ClockedTables.nonpawn.go(
              0n, current, kind, squares,
              paths, zero)),
        100n, clock,
        Equal.sym(Nat, clock, 100n,
          clock_eq),
        Laws.minimax_nonpawn_base_certified(
          paths, kind, squares, zero))
    case 1n++rest:
      +next_clock = {1n+clock : Nat}
      +next = ClockedTables.nonpawn.go(
        rest, next_clock, kind, squares,
        paths, zero)
      next_budget = Equal.trans(Nat,
        Nat.add(next_clock, rest),
        Nat.add(clock, 1n+rest),
        100n,
        Equal.sym(Nat,
          Nat.add(clock, 1n+rest),
          Nat.add(next_clock, rest),
          Laws.nat_add_succ_right(
            clock, rest)),
        budget)
      next_cert =
        Laws.minimax_nonpawn_go_certified(
          rest, next_clock, kind,
          squares, paths, cover, zero,
          no_pawn, next_budget)
      Laws.minimax_nonpawn_layer_certified(
        paths, paths, cover, rest,
        clock, kind, squares, next,
        zero, next_cert, no_pawn)

def Laws.exact_zero_push_white_pawn_is_draw(
  remaining, squares, wk, bk, pc):
  match remaining:
    case 0n:
      {==}
    case 1n+rest:
      {==}

def Laws.exact_zero_push_black_pawn_is_draw(
  remaining, squares, wk, bk, pc):
  match remaining:
    case 0n:
      {==}
    case 1n+rest:
      {==}

def Laws.exact_zero_push_canonical_low_is_draw(
  low, remaining, squares):
  match low:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}:
      +index = {U32{Encoding.append(13n,
        19n, low, Word.zero(13n))} : U32}
      Laws.exact_zero_push_white_pawn_is_draw(
        remaining, squares,
        U32.and(index, 63),
        U32.and(U32.shrn(index, 6n), 63),
        U32.and(U32.shrn(index, 12n), 63))
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{True{}, WNil{}}}}}}}}}}}}}}}}}}}}:
      +index = {U32{Encoding.append(13n,
        19n, low, Word.zero(13n))} : U32}
      Laws.exact_zero_push_black_pawn_is_draw(
        remaining, squares,
        U32.and(index, 63),
        U32.and(U32.shrn(index, 6n), 63),
        U32.and(U32.shrn(index, 12n), 63))

def Laws.exact_pawn_zero_budget_certified(
  paths, remaining, squares):
  match paths:
    case PathTree.Leaf{path}:
      Equal.sym(U32,
        Bool.pick(U32,
          Exact.value(0n, remaining,
            squares, 4,
            Rules.decode(
              Minimax.index_of_path(path))),
          1, 0),
        0,
        Equal.cong(Bool, U32,
          value => Bool.pick(U32,
            value, 1, 0),
          Exact.value(0n, remaining,
            squares, 4,
            Rules.decode(
              Minimax.index_of_path(path))),
          False{},
          Laws.exact_zero_push_canonical_low_is_draw(
            ClockedIndex.reverse(19n,
              path),
            remaining, squares)))
    case PathTree.Node{left, right}:
      Laws.Both{
        Laws.exact_pawn_zero_budget_certified(
          left, remaining, squares),
        Laws.exact_pawn_zero_budget_certified(
          right, remaining, squares)}

def Laws.exact_pawn_clock100_white_step_matches(
  push_rest, wk, bk, pc, squares,
  next, reset, queen, rook):
  Laws.clocked_step_at_hundred_white_is_draw(
    4, wk, bk, pc, squares,
    next, reset, queen, rook)

def exact_pawn_clock100_black_is_minimax(
  +push_rest: Nat, +wk: U32,
  +bk: U32, +pc: U32,
  +squares: List<&2, U32>) ->
  {Minimax.value(0n, 100n, squares,
    4, Rules.State{wk, bk, pc, 1}) ==
    Exact.value(1n+push_rest, 0n,
      squares, 4,
      Rules.State{wk, bk, pc, 1}) : Bool}:
  {==}

def Laws.exact_pawn_clock100_black_step_matches(
  push_rest, wk, bk, pc, squares,
  next, reset, queen, rook):
  +state = {Rules.State{wk, bk, pc,
    1} : Rules.State}
  +middle = Rules.valid(4, state) &&
    Bool.not(U32.is_eq(4, 2)) &&
    Bool.not(U32.is_eq(4, 3)) &&
    ClockedStep.black_terminal(4,
      wk, bk, pc, squares)
  Equal.trans(Bool,
    ClockedStep.value(4, 100n, state,
      squares, next, reset, queen,
      rook),
    middle,
    Exact.value(1n+push_rest, 0n,
      squares, 4, state),
    Laws.clocked_step_at_hundred_black_is_mate(
      4, wk, bk, pc, squares,
      next, reset, queen, rook),
    Equal.trans(Bool, middle,
      ClockedStep.value(4, 100n,
        state, squares, next,
        next, next, next),
      Exact.value(1n+push_rest, 0n,
        squares, 4, state),
      Equal.sym(Bool,
        ClockedStep.value(4, 100n,
          state, squares, next,
          next, next, next),
        middle,
        Laws.clocked_step_at_hundred_black_is_mate(
          4, wk, bk, pc, squares,
          next, next, next, next)),
      Equal.trans(Bool,
        ClockedStep.value(4, 100n,
          state, squares, next,
          next, next, next),
        Minimax.value(0n, 100n,
          squares, 4, state),
        Exact.value(1n+push_rest,
          0n, squares, 4, state),
        Laws.minimax_zero_horizon_black_matches_clock100_step(
          4, squares, wk, bk, pc,
          next),
        exact_pawn_clock100_black_is_minimax(
          push_rest, wk, bk, pc,
          squares))))

def Laws.exact_pawn_clock100_canonical_low_matches(
  low, push_rest, squares, next,
  reset, queen, rook):
  match low:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}:
      +index = {U32{Encoding.append(13n,
        19n, low, Word.zero(13n))} : U32}
      Laws.exact_pawn_clock100_white_step_matches(
        push_rest,
        U32.and(index, 63),
        U32.and(U32.shrn(index, 6n), 63),
        U32.and(U32.shrn(index, 12n), 63),
        squares, next, reset, queen, rook)
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{True{}, WNil{}}}}}}}}}}}}}}}}}}}}:
      +index = {U32{Encoding.append(13n,
        19n, low, Word.zero(13n))} : U32}
      Laws.exact_pawn_clock100_black_step_matches(
        push_rest,
        U32.and(index, 63),
        U32.and(U32.shrn(index, 6n), 63),
        U32.and(U32.shrn(index, 12n), 63),
        squares, next, reset, queen, rook)

def Laws.exact_pawn_clock_base_certified(
  paths, push_rest, squares, zero,
  reset, queen, rook):
  match paths:
    case PathTree.Leaf{path}:
      Equal.cong(Bool, U32,
        value => Bool.pick(U32, value, 1, 0),
        ClockedStep.value(4, 100n,
          Rules.decode(
            Minimax.index_of_path(path)),
          squares, zero, reset,
          queen, rook),
        Exact.value(1n+push_rest, 0n,
          squares, 4,
          Rules.decode(
            Minimax.index_of_path(path))),
        Laws.exact_pawn_clock100_canonical_low_matches(
          ClockedIndex.reverse(19n,
            path), push_rest, squares,
          zero, reset, queen, rook))
    case PathTree.Node{left, right}:
      Laws.Both{
        Laws.exact_pawn_clock_base_certified(
          left, push_rest, squares,
          zero, reset, queen, rook),
        Laws.exact_pawn_clock_base_certified(
          right, push_rest, squares,
          zero, reset, queen, rook)}

def Laws.exact_pawn_clock_go_certified(
  remaining, clock, push_rest,
  squares, paths, cover, reset,
  queen, rook, zero, reset_cert,
  queen_cert, rook_cert, budget):
  match remaining:
    case 0n:
      clock_eq = Equal.trans(Nat,
        clock, Nat.add(clock, 0n),
        100n,
        Equal.sym(Nat,
          Nat.add(clock, 0n), clock,
          Laws.nat_add_right_zero(clock)),
        budget)
      equality_cast(Nat,
        current =>
          Laws.ExactPawnPathCorrect(
            1n+push_rest, 0n,
            squares, paths,
            ClockedTables.pawn.clock.go(
              0n, current, squares,
              paths, reset, queen,
              rook, zero)),
        100n, clock,
        Equal.sym(Nat, clock, 100n,
          clock_eq),
        Laws.exact_pawn_clock_base_certified(
          paths, push_rest, squares,
          zero, reset, queen, rook))
    case 1n++rest:
      +next_clock = {1n+clock : Nat}
      +next = ClockedTables.pawn.clock.go(
        rest, next_clock, squares,
        paths, reset, queen, rook,
        zero)
      next_budget = Equal.trans(Nat,
        Nat.add(next_clock, rest),
        Nat.add(clock, 1n+rest),
        100n,
        Equal.sym(Nat,
          Nat.add(clock, 1n+rest),
          Nat.add(next_clock, rest),
          Laws.nat_add_succ_right(
            clock, rest)),
        budget)
      next_cert =
        Laws.exact_pawn_clock_go_certified(
          rest, next_clock,
          push_rest, squares, paths,
          cover, reset, queen, rook,
          zero, reset_cert,
          queen_cert, rook_cert,
          next_budget)
      Laws.exact_pawn_layer_certified(
        paths, paths, cover,
        push_rest, rest, clock,
        squares, next, reset,
        queen, rook, next_cert,
        reset_cert, queen_cert,
        rook_cert, budget)

def Laws.exact_pawn_budget_go_certified(
  pushes, squares, paths, cover,
  queen, rook, zero, queen_cert,
  rook_cert):
  match pushes:
    case 0n:
      Laws.exact_pawn_zero_budget_certified(
        paths, 100n, squares)
    case 1n+rest:
      +reset =
        ClockedTables.pawn.budget.go(
          rest, squares, paths,
          queen, rook, zero)
      reset_cert =
        Laws.exact_pawn_budget_go_certified(
          rest, squares, paths,
          cover, queen, rook, zero,
          queen_cert, rook_cert)
      Laws.exact_pawn_clock_go_certified(
        100n, 0n, rest,
        squares, paths, cover,
        reset, queen, rook, zero,
        reset_cert, queen_cert,
        rook_cert, {==})

def Laws.generated_nonpawn_value_is_minimax(
  remaining, clock, kind, squares,
  paths, cover, zero, no_pawn,
  budget, state, valid):
  +table = ClockedTables.nonpawn.go(
    remaining, clock, kind,
    squares, paths, zero)
  cert = Laws.minimax_nonpawn_go_certified(
    remaining, clock, kind,
    squares, paths, cover, zero,
    no_pawn, budget)
  Laws.minimax_canonical_path_correct_valid_state_bool(
    paths, cover, table,
    remaining, clock, kind,
    squares, cert, state, valid)

def Laws.generated_pawn_value_is_exact(
  pushes, squares, paths, cover,
  queen, rook, zero,
  queen_cert, rook_cert,
  state, valid):
  +table = ClockedTables.pawn.budget.go(
    pushes, squares, paths,
    queen, rook, zero)
  cert =
    Laws.exact_pawn_budget_go_certified(
      pushes, squares, paths,
      cover, queen, rook, zero,
      queen_cert, rook_cert)
  Laws.exact_pawn_path_correct_valid_state_bool(
    paths, cover, table,
    pushes, 100n, squares,
    cert, state, valid)

def Laws.generated_nonpawn_byte_is_minimax(
  remaining, clock, kind, squares,
  paths, cover, full, zero,
  no_pawn, budget, bits):
  +table = ClockedTables.nonpawn.go(
    remaining, clock, kind,
    squares, paths, zero)
  +expected = Minimax.value_at_path(
    remaining, clock, squares,
    kind, PathTree.get(19n,
      Word(19n), paths, bits))
  table_full = Laws.nonpawn_go_is_full(
    remaining, clock, kind,
    squares, paths, full, zero)
  cert = Laws.minimax_nonpawn_go_certified(
    remaining, clock, kind,
    squares, paths, cover, zero,
    no_pawn, budget)
  Equal.trans(Maybe<&2, U32>,
    List.get(&2, U32,
      ProofTree.bytes(table),
      ProofTree.byte_offset(19n,
        bits)),
    Some{ProofTree.get(19n,
      table, bits)},
    Some{expected},
    Laws.proof_tree_byte_at_path(
      19n, table, table_full,
      bits),
    Equal.cong(U32,
      Maybe<&2, U32>,
      value => Some{value},
      ProofTree.get(19n,
        table, bits),
      expected,
      Laws.minimax_path_correct_lookup(
        19n, remaining,
        clock, kind, squares,
        paths, table, cert,
        bits)))

def Laws.generated_pawn_byte_is_exact(
  pushes, squares, paths, cover,
  full, queen, rook, zero,
  queen_cert, rook_cert, bits):
  +table =
    ClockedTables.pawn.budget.go(
      pushes, squares, paths,
      queen, rook, zero)
  +expected = Exact.pawn_value_at_path(
    pushes, 100n, squares,
    PathTree.get(19n,
      Word(19n), paths, bits))
  table_full =
    Laws.pawn_budget_go_is_full(
      pushes, squares, paths,
      full, queen, rook, zero)
  cert =
    Laws.exact_pawn_budget_go_certified(
      pushes, squares, paths,
      cover, queen, rook, zero,
      queen_cert, rook_cert)
  Equal.trans(Maybe<&2, U32>,
    List.get(&2, U32,
      ProofTree.bytes(table),
      ProofTree.byte_offset(19n,
        bits)),
    Some{ProofTree.get(19n,
      table, bits)},
    Some{expected},
    Laws.proof_tree_byte_at_path(
      19n, table, table_full,
      bits),
    Equal.cong(U32,
      Maybe<&2, U32>,
      value => Some{value},
      ProofTree.get(19n,
        table, bits),
      expected,
      Laws.exact_pawn_path_correct_lookup(
        19n, pushes, 100n,
        squares, paths, table,
        cert, bits)))

def Laws.generated_nonpawn_byte_canonical(
  remaining, clock, kind, squares,
  paths, cover, full, zero,
  no_pawn, budget, bits):
  +found = PathTree.get(19n,
    Word(19n), paths, bits)
  Equal.trans(Maybe<&2, U32>,
    List.get(&2, U32,
      ProofTree.bytes(
        ClockedTables.nonpawn.go(
          remaining, clock,
          kind, squares, paths,
          zero)),
      ProofTree.byte_offset(19n,
        bits)),
    Some{Minimax.value_at_path(
      remaining, clock, squares,
      kind, found)},
    Some{Minimax.value_at_path(
      remaining, clock, squares,
      kind, bits)},
    Laws.generated_nonpawn_byte_is_minimax(
      remaining, clock, kind,
      squares, paths, cover,
      full, zero, no_pawn,
      budget, bits),
    Equal.cong(Word(19n),
      Maybe<&2, U32>,
      path => Some{
        Minimax.value_at_path(
          remaining, clock,
          squares, kind, path)},
      found, bits,
      Laws.canonical_coverage_lookup(
        19n, paths, cover,
        bits)))

def Laws.generated_pawn_byte_canonical(
  pushes, squares, paths, cover,
  full, queen, rook, zero,
  queen_cert, rook_cert, bits):
  +found = PathTree.get(19n,
    Word(19n), paths, bits)
  Equal.trans(Maybe<&2, U32>,
    List.get(&2, U32,
      ProofTree.bytes(
        ClockedTables.pawn.budget.go(
          pushes, squares, paths,
          queen, rook, zero)),
      ProofTree.byte_offset(19n,
        bits)),
    Some{Exact.pawn_value_at_path(
      pushes, 100n, squares,
      found)},
    Some{Exact.pawn_value_at_path(
      pushes, 100n, squares,
      bits)},
    Laws.generated_pawn_byte_is_exact(
      pushes, squares, paths,
      cover, full, queen, rook,
      zero, queen_cert,
      rook_cert, bits),
    Equal.cong(Word(19n),
      Maybe<&2, U32>,
      path => Some{
        Exact.pawn_value_at_path(
          pushes, 100n,
          squares, path)},
      found, bits,
      Laws.canonical_coverage_lookup(
        19n, paths, cover,
        bits)))

def Laws.generated_nonpawn_serialized_valid_state(
  remaining, clock, kind,
  squares, paths, cover,
  full, zero, no_pawn,
  budget, state, valid):
  +table = ClockedTables.nonpawn.go(
    remaining, clock, kind,
    squares, paths, zero)
  +index = Rules.index(state)
  +bits = ProofTree.bits19(index)
  +expected = Bool.pick(U32,
    Minimax.value(remaining,
      clock, squares, kind,
      state), 1, 0)
  table_full = Laws.nonpawn_go_is_full(
    remaining, clock, kind,
    squares, paths, full, zero)
  cert = Laws.minimax_nonpawn_go_certified(
    remaining, clock, kind,
    squares, paths, cover,
    zero, no_pawn, budget)
  Equal.trans(Maybe<&2, U32>,
    List.get(&2, U32,
      ProofTree.bytes(table),
      ProofTree.byte_offset(19n,
        bits)),
    Some{ProofTree.get_index(
      table, index)},
    Some{expected},
    Laws.proof_tree_byte_at_path(
      19n, table, table_full,
      bits),
    Equal.cong(U32,
      Maybe<&2, U32>,
      value => Some{value},
      ProofTree.get_index(table,
        index), expected,
      Laws.minimax_path_correct_valid_state(
        paths,
        bits => Laws.canonical_coverage_lookup(
          19n, paths, cover, bits),
        table,
        remaining, clock, kind,
        squares, cert,
        state, valid)))

def Laws.generated_pawn_serialized_valid_state(
  pushes, squares, paths,
  cover, full, queen, rook,
  zero, queen_cert,
  rook_cert, state, valid):
  +table =
    ClockedTables.pawn.budget.go(
      pushes, squares, paths,
      queen, rook, zero)
  +index = Rules.index(state)
  +bits = ProofTree.bits19(index)
  +expected = Bool.pick(U32,
    Exact.value(pushes,
      100n, squares, 4,
      state), 1, 0)
  table_full =
    Laws.pawn_budget_go_is_full(
      pushes, squares, paths,
      full, queen, rook, zero)
  cert =
    Laws.exact_pawn_budget_go_certified(
      pushes, squares, paths,
      cover, queen, rook, zero,
      queen_cert, rook_cert)
  Equal.trans(Maybe<&2, U32>,
    List.get(&2, U32,
      ProofTree.bytes(table),
      ProofTree.byte_offset(19n,
        bits)),
    Some{ProofTree.get_index(
      table, index)},
    Some{expected},
    Laws.proof_tree_byte_at_path(
      19n, table, table_full,
      bits),
    Equal.cong(U32,
      Maybe<&2, U32>,
      value => Some{value},
      ProofTree.get_index(table,
        index), expected,
      Laws.exact_pawn_path_correct_valid_state(
        paths, cover, table,
        pushes, 100n,
        squares, cert,
        state, valid)))

def Laws.white_king_move_destination_in_range(
  kind, wk, bk, pc, dest, legal):
  target = white_target_valid_from_move(kind,
    wk, bk, pc, dest, bk, pc, legal)
  state_range_wk(dest, bk, pc, 1,
    Laws.legal_state_squares_are_in_reverse_search_range(
      kind, Rules.State{dest, bk, pc, 1}, target))

def Laws.white_piece_move_destination_in_range(
  kind, wk, bk, pc, dest, legal):
  target = white_target_valid_from_move(kind,
    wk, bk, pc, wk, bk, dest, legal)
  state_range_pc(wk, bk, dest, 1,
    Laws.legal_state_squares_are_in_reverse_search_range(
      kind, Rules.State{wk, bk, dest, 1}, target))

def Laws.white_king_winning_square_is_scanned(
  squares, kind, wk, bk, pc, dest, next,
  member, legal, yes):
  match squares:
    case Nil{}:
      match member:
    case +head <> rest:
      match member:
        case Inl{+equal}:
          Inl{(
            equality_cast(U32,
              square => Laws.Truth(Rules.move_to(
                kind, Rules.State{wk, bk, pc, 0},
                Rules.State{square, bk, pc, 1})),
              dest, head, equal, legal),
            equality_cast(U32,
              square => Laws.Truth(U32.is_ne(
                ProofTree.get_index(next,
                  Rules.index(Rules.State{
                    square, bk, pc, 1})), 0)),
              dest, head, equal, yes))}
        case Inr{later}:
          Inr{Laws.white_king_winning_square_is_scanned(
            rest, kind, wk, bk, pc, dest,
            next, later, legal, yes)}

def Laws.white_piece_winning_square_is_scanned(
  squares, kind, wk, bk, pc, dest, next,
  reset, member, legal, yes):
  match squares:
    case Nil{}:
      match member:
    case +head <> rest:
      match member:
        case Inl{+equal}:
          Inl{(
            equality_cast(U32,
              square => Laws.Truth(Rules.move_to(
                kind, Rules.State{wk, bk, pc, 0},
                Rules.State{wk, bk, square, 1})),
              dest, head, equal, legal),
            equality_cast(U32,
              square => Laws.Truth(U32.is_ne(
                ClockedStep.white_piece.value(
                  kind, pc, square,
                  Rules.State{wk, bk, square, 1},
                  next, reset), 0)),
              dest, head, equal, yes))}
        case Inr{later}:
          Inr{Laws.white_piece_winning_square_is_scanned(
            rest, kind, wk, bk, pc, dest,
            next, reset, later, legal, yes)}

def black_capture_dest_range(+kind: U32, +wk: U32,
  +bk: U32, +pc: U32, +dest: U32,
  valid: Laws.Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, 1})),
  capture: Laws.Truth(U32.is_eq(dest, pc))) ->
  Laws.Truth(U32.is_lt(dest, 64)):
  pc_range = state_range_pc(wk, bk, pc, 1,
    Laws.legal_state_squares_are_in_reverse_search_range(
      kind, Rules.State{wk, bk, pc, 1}, valid))
  equal = Laws.u32_equality_reflects_identity(dest, pc, capture)
  equality_cast(U32,
    x => Laws.Truth(U32.is_lt(x, 64)), pc, dest,
    Equal.sym(U32, dest, pc, equal), pc_range)

def black_quiet_dest_range(+kind: U32, +wk: U32,
  +bk: U32, +pc: U32, +dest: U32,
  valid: Laws.Truth(Rules.valid(kind,
    Rules.State{wk, dest, pc, 0}))) ->
  Laws.Truth(U32.is_lt(dest, 64)):
  state_range_bk(wk, dest, pc,
    Laws.legal_state_squares_are_in_reverse_search_range(
      kind, Rules.State{wk, dest, pc, 0}, valid))

def Laws.legal_black_move_destination_in_range(kind, wk,
  bk, pc, dest, valid, move):
  +capture = U32.is_eq(dest, pc)
  +quiet = Rules.valid(kind,
    Rules.State{wk, dest, pc, 0})
  exit = and_right(
    Rules.king_step(bk, dest) &&
      Bool.not(Position.kings_touch(wk, dest)),
    capture || quiet, move)
  or_cases(Laws.Truth(U32.is_lt(dest, 64)),
    capture, quiet, exit,
    capture_proof => black_capture_dest_range(
      kind, wk, bk, pc, dest, valid, capture_proof),
    quiet_proof => black_quiet_dest_range(
      kind, wk, bk, pc, dest, quiet_proof))

def black_scan_squares_sound_to_global_one(
  +squares: List<&2, U32>,
  +kind: U32, +wk: U32, +bk: U32, +pc: U32,
  +won: ProofTree.Tree, +dest: U32,
  valid: Laws.Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, 1})),
  complete: @square: U32 ->
    Laws.Truth(U32.is_lt(square, 64)) ->
    Squares.Member(U32, square, squares),
  safe: Laws.BlackScanSquares(squares, kind,
    wk, bk, pc, won),
  +move: Laws.Truth(Rules.black_move(kind,
    wk, bk, pc, dest))) ->
  Laws.Truth(Bool.not(U32.is_eq(dest, pc))) &
  Laws.Truth(U32.is_ne(ProofTree.get_index(won,
    Rules.index(Rules.State{wk, dest, pc, 0})), 0)):
  range = Laws.legal_black_move_destination_in_range(
    kind, wk, bk, pc, dest, valid, move)
  member = complete(dest, range)
  Laws.black_scan_safe_member(squares, kind, wk,
    bk, pc, dest, won, member, safe, move)

def Laws.black_scan_squares_sound_to_global(
  squares, kind, wk, bk, pc, won, valid,
  complete, safe):
  dest => move =>
    black_scan_squares_sound_to_global_one(
      squares, kind, wk, bk, pc, won, dest,
      valid, complete, safe, move)

def clocked_step_black_terminal_no_move_dest(
  +squares: List<&2, U32>,
  +kind: U32, +wk: U32, +bk: U32, +pc: U32,
  +dest: U32,
  +valid: Laws.Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, 1})),
  complete: @dest: U32 ->
    Laws.Truth(U32.is_lt(dest, 64)) ->
    Squares.Member(U32, dest, squares),
  no_scan: Laws.Truth(Bool.not(
    Retro.black_has_move.squares(kind, wk, bk,
      pc, squares, False{}))),
  +legal: Laws.Truth(Rules.black_move(kind, wk,
    bk, pc, dest))) -> Empty:
  range = Laws.legal_black_move_destination_in_range(
    kind, wk, bk, pc, dest, valid, legal)
  member = complete(dest, range)
  square_legal = Laws.black_scan_legal_member(
    squares, kind, wk, bk, pc, dest,
    member, legal)
  yes = Laws.black_has_move_squares_complete(
    squares, kind, wk, bk, pc,
    False{}, square_legal)
  truth_and_not(
    Retro.black_has_move.squares(kind, wk, bk,
      pc, squares, False{}), yes, no_scan)

def clocked_step_black_terminal_no_move_witness(
  +squares: List<&2, U32>,
  +kind: U32, +wk: U32, +bk: U32, +pc: U32,
  +valid: Laws.Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, 1})),
  complete: @dest: U32 ->
    Laws.Truth(U32.is_lt(dest, 64)) ->
    Squares.Member(U32, dest, squares),
  no_scan: Laws.Truth(Bool.not(
    Retro.black_has_move.squares(kind, wk, bk,
      pc, squares, False{}))),
  witness: Laws.BlackLegalWitness(kind, wk, bk, pc)) -> Empty:
  match witness:
    case (dest, legal):
      clocked_step_black_terminal_no_move_dest(
        squares, kind, wk, bk, pc, dest,
        valid, complete, no_scan, legal)

def clocked_step_black_terminal_no_move(
  +squares: List<&2, U32>,
  +kind: U32, +wk: U32, +bk: U32, +pc: U32,
  +valid: Laws.Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, 1})),
  complete: @dest: U32 ->
    Laws.Truth(U32.is_lt(dest, 64)) ->
    Squares.Member(U32, dest, squares),
  no_scan: Laws.Truth(Bool.not(
    Retro.black_has_move.squares(kind, wk, bk,
      pc, squares, False{}))),
  game_move: WDL.BlackHasMove(kind, wk, bk, pc)) -> Empty:
  clocked_step_black_terminal_no_move_witness(
    squares, kind, wk, bk, pc, valid, complete,
    no_scan,
    Laws.game_black_move_has_legal_destination(
      kind, wk, bk, pc, game_move))

def Laws.clocked_step_black_terminal_sound(
  squares, kind, wk, bk, pc, valid, complete,
  terminal):
  no_scan = and_left(Bool.not(
    Retro.black_has_move.squares(kind, wk, bk,
      pc, squares, False{})),
    Rules.attacks(kind, pc, bk, wk), terminal)
  attacks = and_right(Bool.not(
    Retro.black_has_move.squares(kind, wk, bk,
      pc, squares, False{})),
    Rules.attacks(kind, pc, bk, wk), terminal)
  Tuple{laws_truth_to_wdl_truth(
    Rules.valid(kind, Rules.State{wk, bk, pc, 1}),
    valid),
    Tuple{laws_truth_to_wdl_truth(
      Rules.attacks(kind, pc, bk, wk), attacks),
      game_move => clocked_step_black_terminal_no_move(
        squares, kind, wk, bk, pc, valid,
        complete, no_scan,
        game_move)}}

def bool_not_from_refutation(+value: Bool,
  refute: Laws.Truth(value) -> Empty) ->
  Laws.Truth(Bool.not(value)):
  match value:
    case True{}:
      refute(Unit{})
    case False{}:
      Unit{}

def Laws.legal_pawn_piece_move_changes_square(
  wk, bk, pc, dest, legal):
  bool_not_from_refutation(
    U32.is_eq(pc, dest),
    same =>
      Laws.white_same_class_move_changes_king_or_piece(
        4, wk, bk, pc, wk, bk,
        dest, legal,
        Laws.u32_equality_reflexive(
          wk), same))

def Laws.legal_pawn_piece_move_resets_clock(
  wk, bk, pc, dest, legal):
  and_intro(U32.is_eq(4, 4),
    U32.is_ne(pc, dest),
    Laws.u32_equality_reflexive(4),
    Laws.legal_pawn_piece_move_changes_square(
      wk, bk, pc, dest,
      legal))

def clocked_step_black_terminal_complete_refute(
  +squares: List<&2, U32>,
  +kind: U32, +wk: U32, +bk: U32, +pc: U32,
  valid: WDL.Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, 1})),
  no_moves: WDL.BlackHasMove(kind, wk, bk, pc) -> Empty,
  yes: Laws.Truth(Retro.black_has_move.squares(
    kind, wk, bk, pc, squares, False{}))) -> Empty:
  legal = Laws.black_has_move_squares_sound(
    squares, kind, wk, bk, pc, yes)
  witness = Laws.black_legal_squares_has_witness(
    squares, kind, wk, bk, pc, legal)
  game_move = Laws.black_legal_witness_is_a_game_move(
    kind, wk, bk, pc,
    wdl_truth_to_laws_truth(Rules.valid(kind,
      Rules.State{wk, bk, pc, 1}), valid),
    witness)
  no_moves(game_move)

def Laws.clocked_step_black_terminal_complete(
  squares, kind, wk, bk, pc, mate):
  match mate:
    case Tuple{valid, Tuple{attacks, no_moves}}:
      no_scan = bool_not_from_refutation(
        Retro.black_has_move.squares(kind, wk, bk,
          pc, squares, False{}),
        yes => clocked_step_black_terminal_complete_refute(
          squares, kind, wk, bk, pc, valid,
          no_moves, yes))
      and_intro(Bool.not(
        Retro.black_has_move.squares(kind, wk, bk,
          pc, squares, False{})),
        Rules.attacks(kind, pc, bk, wk), no_scan,
        wdl_truth_to_laws_truth(
          Rules.attacks(kind, pc, bk, wk), attacks))

def Laws.minimax_mate_sound(
  squares, kind, wk, bk, pc,
  complete, mate):
  +new = Minimax.has_move(squares,
    kind, wk, bk, pc, False{})
  +old = Retro.black_has_move.squares(
    kind, wk, bk, pc, squares, False{})
  +attack = Rules.attacks(kind, pc, bk, wk)
  valid = and_left(
    Rules.valid(kind, Rules.State{wk, bk, pc, 1}),
    Bool.not(new) && attack, mate)
  mini_terminal = and_right(
    Rules.valid(kind, Rules.State{wk, bk, pc, 1}),
    Bool.not(new) && attack, mate)
  scan_terminal = equality_cast(Bool,
    Laws.Truth, Bool.not(new) && attack,
    Bool.not(old) && attack,
    Equal.cong(Bool, Bool,
      value => value && attack,
      Bool.not(new), Bool.not(old),
      Equal.cong(Bool, Bool,
        value => Bool.not(value),
        new, old,
        Laws.minimax_has_move_matches_executable_scan(
          squares, kind, wk, bk, pc,
          False{}))), mini_terminal)
  Laws.clocked_step_black_terminal_sound(
    squares, kind, wk, bk, pc,
    valid, complete, scan_terminal)

def Laws.minimax_mate_complete(
  squares, kind, wk, bk, pc, mate):
  match mate:
    case Tuple{+valid, Tuple{attacks, no_moves}}:
      +new = Minimax.has_move(squares,
        kind, wk, bk, pc, False{})
      +old = Retro.black_has_move.squares(
        kind, wk, bk, pc, squares, False{})
      +attack = Rules.attacks(kind, pc, bk, wk)
      scan_terminal =
        Laws.clocked_step_black_terminal_complete(
          squares, kind, wk, bk, pc,
          Tuple{valid, Tuple{attacks, no_moves}})
      mini_terminal = equality_cast(Bool,
        Laws.Truth, Bool.not(old) && attack,
        Bool.not(new) && attack,
        Equal.cong(Bool, Bool,
          value => value && attack,
          Bool.not(old), Bool.not(new),
          Equal.cong(Bool, Bool,
            value => Bool.not(value),
            old, new,
            Equal.sym(Bool, new, old,
              Laws.minimax_has_move_matches_executable_scan(
                squares, kind, wk, bk, pc,
                False{})))), scan_terminal)
      and_intro(
        Rules.valid(kind,
          Rules.State{wk, bk, pc, 1}),
        Bool.not(new) && attack,
        wdl_truth_to_laws_truth(
          Rules.valid(kind,
            Rules.State{wk, bk, pc, 1}),
          valid), mini_terminal)

def Laws.minimax_zero_nonpawn_sound(
  squares, kind, wk, bk, pc,
  clock, complete, yes):
  +valid = Rules.valid(kind,
    Rules.State{wk, bk, pc, 1})
  +b = Bool.not(U32.is_eq(kind, 2))
  +n = Bool.not(U32.is_eq(kind, 3))
  +no_move = Bool.not(Minimax.has_move(
    squares, kind, wk, bk, pc,
    False{}))
  +attack = Rules.attacks(kind, pc, bk, wk)
  +first = valid && b
  +second = first && n
  +third = second && no_move
  +first_yes = and_left(first, n,
    and_left(second, no_move,
      and_left(third, attack, yes)))
  valid_yes = and_left(valid, b,
    first_yes)
  no_move_yes = and_right(second,
    no_move,
    and_left(third, attack, yes))
  attack_yes = and_right(third,
    attack, yes)
  Laws.minimax_mate_sound(squares,
    kind, wk, bk, pc, complete,
    and_intro(valid,
      no_move && attack, valid_yes,
      and_intro(no_move, attack,
        no_move_yes, attack_yes)))

def Laws.minimax_zero_nonpawn_complete(
  squares, kind, wk, bk, pc,
  clock, major, mate):
  +valid = Rules.valid(kind,
    Rules.State{wk, bk, pc, 1})
  +b = Bool.not(U32.is_eq(kind, 2))
  +n = Bool.not(U32.is_eq(kind, 3))
  +no_move = Bool.not(Minimax.has_move(
    squares, kind, wk, bk, pc,
    False{}))
  +attack = Rules.attacks(kind, pc, bk, wk)
  +mate_yes = Laws.minimax_mate_complete(
    squares, kind, wk, bk, pc,
    mate)
  valid_yes = and_left(valid,
    no_move && attack, mate_yes)
  +last = and_right(valid,
    no_move && attack, mate_yes)
  no_move_yes = and_left(no_move,
    attack, last)
  attack_yes = and_right(no_move,
    attack, last)
  and_intro(
    ((valid && b) && n) && no_move,
    attack,
    and_intro((valid && b) && n,
      no_move,
      and_intro(valid && b, n,
        and_intro(valid, b,
          valid_yes,
          and_left(b, n, major)),
        and_right(b, n, major)),
      no_move_yes),
    attack_yes)

def guarded_or_from_implies(+guard: Bool,
  +result: Bool,
  implies: Laws.Truth(guard) ->
    Laws.Truth(result)) ->
  Laws.Truth(Bool.not(guard) || result):
  match guard:
    case True{}:
      implies(Unit{})
    case False{}:
      Unit{}

def guarded_or_to_implies(+guard: Bool,
  +result: Bool,
  proof: Laws.Truth(Bool.not(guard) ||
    result),
  yes: Laws.Truth(guard)) ->
  Laws.Truth(result):
  match guard:
    case True{}:
      proof
    case False{}:
      Empty.absurd(Laws.Truth(result),
        yes)

def bool_pick_true_sound(
  +test: Bool, +left: Bool,
  +right: Bool,
  truth: Laws.Truth(test),
  picked: Laws.Truth(Bool.pick(
    Bool, test, left, right))) ->
  Laws.Truth(left):
  match test:
    case True{}:
      picked
    case False{}:
      Empty.absurd(
        Laws.Truth(left), truth)

def bool_pick_true_complete(
  +test: Bool, +left: Bool,
  +right: Bool,
  truth: Laws.Truth(test),
  chosen: Laws.Truth(left)) ->
  Laws.Truth(Bool.pick(Bool,
    test, left, right)):
  match test:
    case True{}:
      chosen
    case False{}:
      Empty.absurd(
        Laws.Truth(right), truth)

def byte_option_is_zero(
  item: Maybe<&2, U32>) -> Bool:
  match item:
    case None{}:
      False{}
    case Some{value}:
      U32.is_eq(value, 0)

def zero_byte_cannot_equal_one(
  same: {Some{0} == Some{1} :
    Maybe<&2, U32>}) -> Empty:
  equality_cast(Maybe<&2, U32>,
    item => Laws.Truth(
      byte_option_is_zero(item)),
    Some{0}, Some{1},
    same, Unit{})

def byte_one_reflects_truth(
  +value: Bool,
  same: {Some{Bool.pick(U32,
    value, 1, 0)} == Some{1} :
    Maybe<&2, U32>}) ->
  Laws.Truth(value):
  match value:
    case True{}:
      Unit{}
    case False{}:
      equality_cast(
        Maybe<&2, U32>,
        item => Laws.Truth(
          byte_option_is_zero(item)),
        Some{0}, Some{1},
        same, Unit{})

def truth_gives_byte_one(
  +value: Bool,
  yes: Laws.Truth(value)) ->
  {Some{Bool.pick(U32,
    value, 1, 0)} == Some{1} :
    Maybe<&2, U32>}:
  match value:
    case True{}:
      {==}
    case False{}:
      Empty.absurd(
        {Some{0} == Some{1} :
          Maybe<&2, U32>},
        yes)

def serialized_byte_one_sound(
  +bytes: List<&2, U32>,
  +offset: Nat, +value: Bool,
  expected: {List.get(&2, U32,
    bytes, offset) ==
    Some{Bool.pick(U32,
      value, 1, 0)} :
    Maybe<&2, U32>},
  read_one: {List.get(&2, U32,
    bytes, offset) ==
    Some{1} : Maybe<&2, U32>}) ->
  Laws.Truth(value):
  byte_one_reflects_truth(value,
    Equal.trans(Maybe<&2, U32>,
      Some{Bool.pick(U32,
        value, 1, 0)},
      List.get(&2, U32,
        bytes, offset),
      Some{1},
      Equal.sym(Maybe<&2, U32>,
        List.get(&2, U32,
          bytes, offset),
        Some{Bool.pick(U32,
          value, 1, 0)},
        expected), read_one))

def serialized_byte_one_complete(
  +bytes: List<&2, U32>,
  +offset: Nat, +value: Bool,
  expected: {List.get(&2, U32,
    bytes, offset) ==
    Some{Bool.pick(U32,
      value, 1, 0)} :
    Maybe<&2, U32>},
  yes: Laws.Truth(value)) ->
  {List.get(&2, U32,
    bytes, offset) ==
    Some{1} : Maybe<&2, U32>}:
  Equal.trans(Maybe<&2, U32>,
    List.get(&2, U32,
      bytes, offset),
    Some{Bool.pick(U32,
      value, 1, 0)},
    Some{1}, expected,
    truth_gives_byte_one(
      value, yes))

def truth_or_split(+left: Bool,
  +right: Bool,
  proof: Laws.Truth(left || right)) ->
  Laws.Truth(left) | Laws.Truth(right):
  or_cases(Laws.Truth(left) |
    Laws.Truth(right), left, right,
    proof,
    yes => Inl{yes},
    yes => Inr{yes})

def positive_nat_eq_zero_absurd(
  +rest: Nat,
  same: {1n+rest == 0n : Nat}) ->
  Empty:
  equality_cast(Nat,
    value => Laws.Truth(
      Nat.is_eq(value, 0n)),
    0n, 1n+rest,
    Equal.sym(Nat,
      1n+rest, 0n, same),
    Unit{})

def two_plus_nat_eq_one_absurd(
  +rest: Nat,
  same: {2n+rest == 1n : Nat}) ->
  Empty:
  equality_cast(Nat,
    value => Laws.Truth(
      Nat.is_eq(value, 1n)),
    1n, 2n+rest,
    Equal.sym(Nat,
      2n+rest, 1n, same),
    Unit{})

def zero_eq_one_absurd(
  same: {0n == 1n : Nat}) ->
  Empty:
  equality_cast(Nat,
    value => Laws.Truth(
      Nat.is_eq(value, 0n)),
    0n, 1n, same, Unit{})

def nonpawn_blackall_sound_finish(
  +rest: Nat, +tail: List<&2, U32>,
  +squares: List<&2, U32>,
  +dest: U32, +kind: U32,
  +wk: U32, +bk: U32,
  +pc: U32, +clock: Nat,
  +all_so_far: Bool,
  later: Resource.NonpawnEvidence(
    1n+rest, 0n, tail,
    squares, kind,
    Resource.BlackAll{wk, bk,
      pc, clock,
      all_so_far &&
        (Bool.not(Rules.black_move(kind,
          wk, bk, pc, dest)) ||
         (U32.is_ne(dest, pc) &&
          Minimax.win(rest, 1n,
            squares,
            squares,
            Minimax.Value{kind,
              Rules.State{wk, dest,
                pc, 0},
              1n+clock})))})
  child_sound: Laws.Truth(Minimax.win(
    rest, 1n, squares,
    squares,
    Minimax.Value{kind,
      Rules.State{wk, dest, pc,
        0}, 1n+clock})) ->
    Resource.Nonpawn(rest,
      1n+clock, squares,
      kind, Rules.State{wk,
        dest, pc, 0})) ->
  Resource.NonpawnEvidence(
    1n+rest, 0n,
    dest <> tail, squares,
    kind, Resource.BlackAll{
      wk, bk, pc, clock,
      all_so_far}):
  match later:
    case (+updated_yes, rest_all):
      +legal = Rules.black_move(kind,
        wk, bk, pc, dest)
      +safe = U32.is_ne(dest, pc)
      +child = Minimax.win(rest,
        1n, squares,
        squares,
        Minimax.Value{kind,
          Rules.State{wk, dest,
            pc, 0}, 1n+clock})
      +implies = Bool.not(legal) ||
        (safe && child)
      +updated = all_so_far &&
        implies
      +guarded = and_right(
        all_so_far, implies,
        wdl_truth_to_laws_truth(
          updated, updated_yes))
      (laws_truth_to_wdl_truth(
         all_so_far,
         and_left(all_so_far,
           implies,
           wdl_truth_to_laws_truth(
             updated,
             updated_yes))),
       (legal_yes =>
          +good =
            guarded_or_to_implies(
              legal, safe && child,
              guarded,
              wdl_truth_to_laws_truth(
                legal, legal_yes))
          (laws_truth_to_wdl_truth(
             safe,
             and_left(safe, child,
               good)),
           child_sound(
             and_right(safe, child,
               good))),
        rest_all))

def nonpawn_blackall_every(
  +fuel: Nat, +clock: Nat,
  +squares: List<&2, U32>,
  +kind: U32, +wk: U32,
  +bk: U32, +pc: U32,
  evidence: Resource.NonpawnEvidence(
    1n+fuel, 0n,
    squares,
    squares, kind,
    Resource.BlackAll{wk, bk,
      pc, clock, True{}})) ->
  Laws.NonpawnBlackEvery(fuel,
    clock, squares,
    kind, wk, bk, pc):
  match evidence:
    case (true_proof, all):
      all

def Laws.nonpawn_strategy_sound(
  fuel, phase, candidates, squares,
  kind, task, phase_eq, same,
  no_pawn,
  yes):
  match fuel phase candidates task:
    case 0n 1n _ Resource.BlackValue{
        wk, bk, pc, clock}:
      Laws.minimax_zero_nonpawn_sound(
        squares, kind,
        wk, bk, pc, clock,
        +dest => bound =>
          Laws.square_list_equals_member_transfer(
            squares, Squares.all6(),
            dest, same,
            Laws.square_list_complete(
              dest, bound)),
        yes)
    case 0n 1n _ Resource.WhiteValue{
        wk, bk, pc, clock}:
      yes
    case 0n 0n _ Resource.King{wk, bk,
        pc, clock}:
      yes
    case 0n 0n _ Resource.Piece{wk, bk,
        pc, clock}:
      yes
    case 0n 0n _ Resource.BlackAll{wk,
        bk, pc, clock,
        all_so_far}:
      yes
    case 1n++rest 0n Nil{} Resource.King{wk,
        bk, pc, clock}:
      yes
    case 1n++rest 0n +dest <> tail
         Resource.King{+wk,
        +bk, +pc, +clock}:
          +legal = Rules.move_to(kind,
            Rules.State{wk, bk, pc,
              0},
            Rules.State{dest, bk, pc,
              1})
          +won = Minimax.win(rest,
            1n, squares,
            squares,
            Minimax.Value{kind,
              Rules.State{dest, bk,
                pc, 1}, 1n+clock})
          +later = Minimax.win(
            1n+rest, 0n, tail,
            squares,
            Minimax.King{kind, wk,
              bk, pc, clock})
          or_cases(
            Resource.NonpawnEvidence(
              1n+rest, 0n,
              dest <> tail,
              squares, kind,
              Resource.King{wk, bk,
                pc, clock}),
            legal && won, later, yes,
            +head => Inl{(
              laws_truth_to_wdl_truth(
                legal,
                and_left(legal, won,
                  head)),
              Laws.nonpawn_strategy_sound(
                rest, 1n,
                squares, squares,
                kind,
                Resource.BlackValue{
                  dest, bk, pc,
                  1n+clock},
                {==},
                same,
                no_pawn,
                and_right(legal,
                  won, head)))},
            rest_yes => Inr{
              Laws.nonpawn_strategy_sound(
                1n+rest, 0n,
                tail, squares,
                kind,
                Resource.King{wk, bk,
                  pc, clock},
                {==},
                same,
                no_pawn, rest_yes)})
    case 1n++rest 0n Nil{} Resource.Piece{wk,
        bk, pc, clock}:
      yes
    case 1n++rest 0n +dest <> tail
         Resource.Piece{+wk,
        +bk, +pc, +clock}:
          +legal = Rules.move_to(kind,
            Rules.State{wk, bk, pc,
              0},
            Rules.State{wk, bk, dest,
              1})
          +next_clock = Bool.pick(Nat,
            U32.is_eq(kind, 4) &&
              U32.is_ne(pc, dest),
            0n, 1n+clock)
          +won = Minimax.win(rest,
            1n, squares,
            squares,
            Minimax.Value{kind,
              Rules.State{wk, bk,
                dest, 1}, next_clock})
          +later = Minimax.win(
            1n+rest, 0n, tail,
            squares,
            Minimax.Piece{kind, wk,
              bk, pc, clock})
          or_cases(
            Resource.NonpawnEvidence(
              1n+rest, 0n,
              dest <> tail,
              squares, kind,
              Resource.Piece{wk, bk,
                pc, clock}),
            legal && won, later, yes,
            +head => Inl{(
              laws_truth_to_wdl_truth(
                legal,
                and_left(legal, won,
                  head)),
              Laws.nonpawn_strategy_sound(
                rest, 1n,
                squares, squares,
                kind,
                Resource.BlackValue{
                  wk, bk, dest,
                  next_clock},
                {==},
                same,
                no_pawn,
                and_right(legal,
                  won, head)))},
            rest_yes => Inr{
              Laws.nonpawn_strategy_sound(
                1n+rest, 0n,
                tail, squares,
                kind,
                Resource.Piece{wk, bk,
                  pc, clock},
                {==},
                same,
                no_pawn, rest_yes)})
    case 1n++rest 0n Nil{} Resource.BlackAll{
        wk, bk, pc, clock,
        all_so_far}:
      (laws_truth_to_wdl_truth(
        all_so_far, yes), Unit{})
    case 1n++rest 0n +dest <> tail
         Resource.BlackAll{+wk,
        +bk, +pc, +clock,
        +all_so_far}:
      +legal = Rules.black_move(kind,
        wk, bk, pc, dest)
      +safe = U32.is_ne(dest, pc)
      +child = Minimax.win(rest,
        1n, squares,
        squares,
        Minimax.Value{kind,
          Rules.State{wk, dest,
            pc, 0}, 1n+clock})
      +implies = Bool.not(legal) ||
        (safe && child)
      +updated = all_so_far &&
        implies
      nonpawn_blackall_sound_finish(
        rest, tail, squares,
        dest, kind,
        wk, bk, pc, clock,
        all_so_far,
        Laws.nonpawn_strategy_sound(
          1n+rest, 0n,
          tail, squares, kind,
          Resource.BlackAll{wk, bk,
            pc, clock, updated},
          {==},
          same,
          no_pawn, yes),
        child_yes =>
          Laws.nonpawn_strategy_sound(
            rest, 1n,
            squares, squares,
            kind,
            Resource.WhiteValue{
              wk, dest, pc,
              1n+clock},
            {==},
            same,
            no_pawn, child_yes))
    case 1n++rest 1n _ Resource.WhiteValue{
        +wk, +bk, +pc, +clock}:
      +valid = Rules.valid(kind,
        Rules.State{wk, bk, pc, 0})
      +bishop = Bool.not(
        U32.is_eq(kind, 2))
      +knight = Bool.not(
        U32.is_eq(kind, 3))
      +before = Nat.is_lt(clock,
        100n)
      +king = Minimax.win(1n+rest,
        0n, squares,
        squares,
        Minimax.King{kind, wk,
          bk, pc, clock})
      +piece = Minimax.win(1n+rest,
        0n, squares,
        squares,
        Minimax.Piece{kind, wk,
          bk, pc, clock})
      +promotion =
        U32.is_eq(kind, 4) &&
        ((WDL.promotion(wk, bk,
            pc, 0, wk, bk,
            (pc + 8 : U32)) &&
          Minimax.win(rest, 1n,
            squares,
            squares,
            Minimax.Value{0,
              Rules.State{wk, bk,
                (pc + 8 : U32),
                1}, 0n})) ||
         (WDL.promotion(wk, bk,
            pc, 1, wk, bk,
            (pc + 8 : U32)) &&
          Minimax.win(rest, 1n,
            squares,
            squares,
            Minimax.Value{1,
              Rules.State{wk, bk,
                (pc + 8 : U32),
                1}, 0n})))
      +move = king || piece
      +choice = move || promotion
      +prefix = ((valid && bishop) &&
        knight) && before
      +prefix_yes = and_left(prefix,
        choice, yes)
      +valid_yes = and_left(valid,
        bishop,
        and_left(valid && bishop,
          knight,
          and_left((valid && bishop) &&
            knight, before,
            prefix_yes)))
      +before_yes = and_right(
        (valid && bishop) &&
          knight, before,
        prefix_yes)
      choice_yes = and_right(prefix,
        choice, yes)
      or_cases(
        Resource.Nonpawn(1n+rest,
          clock, squares,
          kind, Rules.State{wk,
            bk, pc, 0}),
        move, promotion,
        choice_yes,
        move_yes =>
          or_cases(
            Resource.Nonpawn(1n+rest,
              clock, squares,
              kind,
              Rules.State{wk,
                bk, pc, 0}),
            king, piece,
            move_yes,
            king_yes =>
              (laws_truth_to_wdl_truth(
                 valid, valid_yes),
               (laws_truth_to_wdl_truth(
                  before, before_yes),
                Inl{
                  Laws.nonpawn_strategy_sound(
                    1n+rest,
                    0n,
                    squares, squares,
                    kind,
                    Resource.King{
                      wk, bk, pc,
                      clock},
                    {==},
                    same,
                    no_pawn,
                    king_yes)})),
            piece_yes =>
              (laws_truth_to_wdl_truth(
                 valid, valid_yes),
               (laws_truth_to_wdl_truth(
                  before, before_yes),
                Inr{
                  Laws.nonpawn_strategy_sound(
                    1n+rest,
                    0n,
                    squares, squares,
                    kind,
                    Resource.Piece{
                      wk, bk, pc,
                      clock},
                    {==},
                    same,
                    no_pawn,
                    piece_yes)}))),
        promotion_yes =>
          Empty.absurd(
            Resource.Nonpawn(1n+rest,
              clock, squares,
              kind,
              Rules.State{wk,
                bk, pc, 0}),
            true_and_not_absurd(
              U32.is_eq(kind, 4),
              and_left(U32.is_eq(
                  kind, 4),
                (WDL.promotion(wk,
                    bk, pc, 0,
                    wk, bk,
                    (pc + 8 : U32)) &&
                  Minimax.win(rest,
                    1n, squares,
                    squares,
                    Minimax.Value{0,
                      Rules.State{wk,
                        bk,
                        (pc + 8 : U32),
                        1}, 0n})) ||
                (WDL.promotion(wk,
                    bk, pc, 1,
                    wk, bk,
                    (pc + 8 : U32)) &&
                  Minimax.win(rest,
                    1n, squares,
                    squares,
                    Minimax.Value{1,
                      Rules.State{wk,
                        bk,
                        (pc + 8 : U32),
                        1}, 0n})),
                promotion_yes),
              no_pawn)))
    case 1n++rest 1n _ Resource.BlackValue{
        +wk, +bk, +pc, +clock}:
      +valid = Rules.valid(kind,
        Rules.State{wk, bk, pc, 1})
      +bishop = Bool.not(
        U32.is_eq(kind, 2))
      +knight = Bool.not(
        U32.is_eq(kind, 3))
      +has = Minimax.has_move(
        squares, kind,
        wk, bk, pc, False{})
      +attack = Rules.attacks(kind,
        pc, bk, wk)
      +mate = Bool.not(has) && attack
      +before = Nat.is_lt(clock,
        100n)
      +all = Minimax.win(1n+rest,
        0n, squares,
        squares,
        Minimax.BlackAll{kind,
          wk, bk, pc, clock,
          True{}})
      +continuation =
        (before && has) && all
      +body = mate || continuation
      +prefix = (valid && bishop) &&
        knight
      +prefix_yes = and_left(prefix,
        body, yes)
      +valid_yes = and_left(valid,
        bishop,
        and_left(valid && bishop,
          knight, prefix_yes))
      body_yes = and_right(prefix,
        body, yes)
      or_cases(
        Resource.Nonpawn(1n+rest,
          clock, squares,
          kind,
          Rules.State{wk,
            bk, pc, 1}),
        mate, continuation,
        body_yes,
        mate_yes =>
          (laws_truth_to_wdl_truth(
             valid, valid_yes),
           Inl{
             Laws.minimax_mate_sound(
               squares,
               kind, wk, bk, pc,
               +dest => bound =>
                 Laws.square_list_equals_member_transfer(
                   squares,
                   Squares.all6(),
                   dest, same,
                   Laws.square_list_complete(
                     dest, bound)),
               and_intro(valid, mate,
                 valid_yes,
                 mate_yes))}),
        +next_yes =>
          +first = before && has
          +first_yes = and_left(first,
            all, next_yes)
          +has_yes = and_right(before,
            has, first_yes)
          +all_yes = and_right(first,
            all, next_yes)
          (laws_truth_to_wdl_truth(
             valid, valid_yes),
           Inr{(
             laws_truth_to_wdl_truth(
               before,
               and_left(before, has,
                 first_yes)),
             (Laws.minimax_has_move_has_witness(
                squares, kind,
                wk, bk, pc,
                has_yes),
              nonpawn_blackall_every(
                rest, clock, squares,
                kind,
                wk, bk, pc,
                Laws.nonpawn_strategy_sound(
                  1n+rest,
                  0n,
                  squares, squares,
                  kind,
                  Resource.BlackAll{
                    wk, bk, pc,
                    clock, True{}},
                  {==},
                  same,
                  no_pawn,
                  all_yes))))}))
    case fuel 0n candidates Resource.WhiteValue{
        wk, bk, pc, clock}:
      Empty.absurd(
        Resource.NonpawnEvidence(fuel,
          0n, candidates,
          squares, kind,
          Resource.WhiteValue{
            wk, bk, pc, clock}),
        zero_eq_one_absurd(phase_eq))
    case fuel 2n+more candidates Resource.WhiteValue{
        wk, bk, pc, clock}:
      Empty.absurd(
        Resource.NonpawnEvidence(fuel,
          2n+more, candidates,
          squares, kind,
          Resource.WhiteValue{
            wk, bk, pc, clock}),
        two_plus_nat_eq_one_absurd(
          more, phase_eq))
    case fuel 0n candidates Resource.BlackValue{
        wk, bk, pc, clock}:
      Empty.absurd(
        Resource.NonpawnEvidence(fuel,
          0n, candidates,
          squares, kind,
          Resource.BlackValue{
            wk, bk, pc, clock}),
        zero_eq_one_absurd(phase_eq))
    case fuel 2n+more candidates Resource.BlackValue{
        wk, bk, pc, clock}:
      Empty.absurd(
        Resource.NonpawnEvidence(fuel,
          2n+more, candidates,
          squares, kind,
          Resource.BlackValue{
            wk, bk, pc, clock}),
        two_plus_nat_eq_one_absurd(
          more, phase_eq))
    case fuel 1n+more candidates Resource.King{
        wk, bk, pc, clock}:
      Empty.absurd(
        Resource.NonpawnEvidence(fuel,
          1n+more, candidates,
          squares, kind,
          Resource.King{wk, bk,
            pc, clock}),
        positive_nat_eq_zero_absurd(
          more, phase_eq))
    case fuel 1n+more candidates Resource.Piece{
        wk, bk, pc, clock}:
      Empty.absurd(
        Resource.NonpawnEvidence(fuel,
          1n+more, candidates,
          squares, kind,
          Resource.Piece{wk, bk,
            pc, clock}),
        positive_nat_eq_zero_absurd(
          more, phase_eq))
    case fuel 1n+more candidates Resource.BlackAll{
        wk, bk, pc, clock,
        all_so_far}:
      Empty.absurd(
        Resource.NonpawnEvidence(fuel,
          1n+more, candidates,
          squares, kind,
          Resource.BlackAll{
            wk, bk, pc, clock,
            all_so_far}),
        positive_nat_eq_zero_absurd(
          more, phase_eq))

def nonpawn_blackall_complete_head(
  +rest: Nat, +clock: Nat,
  +squares: List<&2, U32>,
  +kind: U32, +wk: U32,
  +bk: U32, +pc: U32,
  +dest: U32,
  good: WDL.Truth(U32.is_ne(dest,
    pc)) & Resource.Nonpawn(rest,
      1n+clock, squares, kind,
      Rules.State{wk, dest,
        pc, 0}),
  child_complete:
    Resource.Nonpawn(rest,
      1n+clock, squares, kind,
      Rules.State{wk, dest,
        pc, 0}) ->
    Laws.Truth(Minimax.win(rest,
      1n, squares, squares,
      Minimax.Value{kind,
        Rules.State{wk, dest,
          pc, 0}, 1n+clock}))) ->
  Laws.Truth(U32.is_ne(dest, pc) &&
    Minimax.win(rest, 1n,
      squares, squares,
      Minimax.Value{kind,
        Rules.State{wk, dest,
          pc, 0}, 1n+clock})):
  match good:
    case (safe_yes, strategy):
      and_intro(U32.is_ne(dest,
          pc),
        Minimax.win(rest, 1n,
          squares, squares,
          Minimax.Value{kind,
            Rules.State{wk, dest,
              pc, 0}, 1n+clock}),
        wdl_truth_to_laws_truth(
          U32.is_ne(dest, pc),
          safe_yes),
        child_complete(strategy))

def nonpawn_major_prefix(
  +kind: U32, +valid: Bool,
  valid_yes: WDL.Truth(valid),
  +major: Laws.Truth(
    Bool.not(U32.is_eq(kind, 2)) &&
    Bool.not(U32.is_eq(kind, 3)))) ->
  Laws.Truth((valid &&
    Bool.not(U32.is_eq(kind, 2))) &&
    Bool.not(U32.is_eq(kind, 3))):
  +bishop = Bool.not(U32.is_eq(
    kind, 2))
  +knight = Bool.not(U32.is_eq(
    kind, 3))
  and_intro(valid && bishop,
    knight,
    and_intro(valid, bishop,
      wdl_truth_to_laws_truth(
        valid, valid_yes),
      and_left(bishop, knight,
        major)),
    and_right(bishop, knight,
      major))

def nonpawn_white_value_complete_finish(
  +rest: Nat, +clock: Nat,
  +squares: List<&2, U32>,
  +kind: U32, +wk: U32,
  +bk: U32, +pc: U32,
  valid_yes: WDL.Truth(
    Rules.valid(kind,
      Rules.State{wk, bk,
        pc, 0})),
  before_yes: WDL.Truth(
    Nat.is_lt(clock, 100n)),
  major: Laws.Truth(
    Bool.not(U32.is_eq(kind, 2)) &&
    Bool.not(U32.is_eq(kind, 3))),
  move_yes: Laws.Truth(
    Minimax.win(1n+rest,
      0n, squares, squares,
      Minimax.King{kind, wk,
        bk, pc, clock}) ||
    Minimax.win(1n+rest,
      0n, squares, squares,
      Minimax.Piece{kind, wk,
        bk, pc, clock}))) ->
  Laws.Truth(Minimax.win(1n+rest,
    1n, squares, squares,
    Minimax.Value{kind,
      Rules.State{wk, bk,
        pc, 0}, clock})):
  +valid = Rules.valid(kind,
    Rules.State{wk, bk, pc, 0})
  +bishop = Bool.not(U32.is_eq(
    kind, 2))
  +knight = Bool.not(U32.is_eq(
    kind, 3))
  +before = Nat.is_lt(clock,
    100n)
  +king = Minimax.win(1n+rest,
    0n, squares, squares,
    Minimax.King{kind, wk,
      bk, pc, clock})
  +piece = Minimax.win(1n+rest,
    0n, squares, squares,
    Minimax.Piece{kind, wk,
      bk, pc, clock})
  +promotion =
    U32.is_eq(kind, 4) &&
    ((WDL.promotion(wk, bk,
        pc, 0, wk, bk,
        (pc + 8 : U32)) &&
      Minimax.win(rest, 1n,
        squares, squares,
        Minimax.Value{0,
          Rules.State{wk, bk,
            (pc + 8 : U32),
            1}, 0n})) ||
     (WDL.promotion(wk, bk,
        pc, 1, wk, bk,
        (pc + 8 : U32)) &&
      Minimax.win(rest, 1n,
        squares, squares,
        Minimax.Value{1,
          Rules.State{wk, bk,
            (pc + 8 : U32),
            1}, 0n})))
  +move = king || piece
  +choice = move || promotion
  +third = (valid && bishop) &&
    knight
  +prefix = third && before
  and_intro(prefix, choice,
    and_intro(third, before,
      nonpawn_major_prefix(kind,
        valid, valid_yes,
        major),
      wdl_truth_to_laws_truth(
        before, before_yes)),
    or_left(move, promotion,
      move_yes))

def nonpawn_black_value_complete_finish(
  +rest: Nat, +clock: Nat,
  +squares: List<&2, U32>,
  +kind: U32, +wk: U32,
  +bk: U32, +pc: U32,
  valid_yes: WDL.Truth(
    Rules.valid(kind,
      Rules.State{wk, bk,
        pc, 1})),
  major: Laws.Truth(
    Bool.not(U32.is_eq(kind, 2)) &&
    Bool.not(U32.is_eq(kind, 3))),
  body_yes: Laws.Truth(
    (Bool.not(Minimax.has_move(
      squares, kind, wk,
      bk, pc, False{})) &&
     Rules.attacks(kind, pc,
       bk, wk)) ||
    ((Nat.is_lt(clock, 100n) &&
       Minimax.has_move(squares,
         kind, wk, bk, pc,
         False{})) &&
     Minimax.win(1n+rest, 0n,
       squares, squares,
       Minimax.BlackAll{kind,
         wk, bk, pc, clock,
         True{}})))) ->
  Laws.Truth(Minimax.win(1n+rest,
    1n, squares, squares,
    Minimax.Value{kind,
      Rules.State{wk, bk,
        pc, 1}, clock})):
  +valid = Rules.valid(kind,
    Rules.State{wk, bk, pc, 1})
  +bishop = Bool.not(U32.is_eq(
    kind, 2))
  +knight = Bool.not(U32.is_eq(
    kind, 3))
  +body =
    (Bool.not(Minimax.has_move(
      squares, kind, wk,
      bk, pc, False{})) &&
     Rules.attacks(kind, pc,
       bk, wk)) ||
    ((Nat.is_lt(clock, 100n) &&
       Minimax.has_move(squares,
         kind, wk, bk, pc,
         False{})) &&
     Minimax.win(1n+rest, 0n,
       squares, squares,
       Minimax.BlackAll{kind,
         wk, bk, pc, clock,
         True{}}))
  and_intro((valid && bishop) &&
      knight, body,
    nonpawn_major_prefix(kind,
      valid, valid_yes, major),
    body_yes)

def Laws.nonpawn_strategy_complete(
  fuel, phase, candidates, squares,
  kind, task, phase_eq, same,
  major, no_pawn, evidence):
  match fuel phase candidates task:
    case 0n 1n _ Resource.BlackValue{
        wk, bk, pc, clock}:
      Laws.minimax_zero_nonpawn_complete(
        squares, kind, wk, bk, pc,
        clock, major, evidence)
    case 0n 1n _ Resource.WhiteValue{
        wk, bk, pc, clock}:
      match evidence:
    case 0n 0n _ Resource.King{
        wk, bk, pc, clock}:
      match evidence:
    case 0n 0n _ Resource.Piece{
        wk, bk, pc, clock}:
      match evidence:
    case 0n 0n _ Resource.BlackAll{
        wk, bk, pc, clock,
        all_so_far}:
      match evidence:
    case 1n++rest 0n Nil{}
         Resource.King{wk, bk,
           pc, clock}:
      match evidence:
    case 1n++rest 0n +dest <> tail
         Resource.King{+wk, +bk,
           +pc, +clock}:
      match evidence:
        case Inl{head}:
          match head:
            case (legal, child):
              +move = Rules.move_to(kind,
                Rules.State{wk, bk,
                  pc, 0},
                Rules.State{dest, bk,
                  pc, 1})
              +won = Minimax.win(rest,
                1n, squares, squares,
                Minimax.Value{kind,
                  Rules.State{dest,
                    bk, pc, 1},
                  1n+clock})
              or_left(move && won,
                Minimax.win(1n+rest,
                  0n, tail, squares,
                  Minimax.King{kind,
                    wk, bk, pc,
                    clock}),
                and_intro(move, won,
                  wdl_truth_to_laws_truth(
                    move, legal),
                  Laws.nonpawn_strategy_complete(
                    rest, 1n,
                    squares, squares,
                    kind,
                    Resource.BlackValue{
                      dest, bk, pc,
                      1n+clock},
                    {==}, same, major,
                    no_pawn, child)))
        case Inr{later}:
          or_right(
            Rules.move_to(kind,
              Rules.State{wk, bk,
                pc, 0},
              Rules.State{dest, bk,
                pc, 1}) &&
            Minimax.win(rest, 1n,
              squares, squares,
              Minimax.Value{kind,
                Rules.State{dest,
                  bk, pc, 1},
                1n+clock}),
            Minimax.win(1n+rest,
              0n, tail, squares,
              Minimax.King{kind,
                wk, bk, pc,
                clock}),
            Laws.nonpawn_strategy_complete(
              1n+rest, 0n,
              tail, squares, kind,
              Resource.King{wk,
                bk, pc, clock},
              {==}, same, major,
              no_pawn, later))
    case 1n++rest 0n Nil{}
         Resource.Piece{wk, bk,
           pc, clock}:
      match evidence:
    case 1n++rest 0n +dest <> tail
         Resource.Piece{+wk, +bk,
           +pc, +clock}:
      match evidence:
        case Inl{head}:
          match head:
            case (legal, child):
              +move = Rules.move_to(kind,
                Rules.State{wk, bk,
                  pc, 0},
                Rules.State{wk, bk,
                  dest, 1})
              +reset = U32.is_eq(kind,
                4) && U32.is_ne(pc,
                  dest)
              +next_clock = Bool.pick(
                Nat, reset, 0n,
                1n+clock)
              +won = Minimax.win(rest,
                1n, squares, squares,
                Minimax.Value{kind,
                  Rules.State{wk, bk,
                    dest, 1},
                  next_clock})
              or_left(move && won,
                Minimax.win(1n+rest,
                  0n, tail, squares,
                  Minimax.Piece{kind,
                    wk, bk, pc,
                    clock}),
                and_intro(move, won,
                  wdl_truth_to_laws_truth(
                    move, legal),
                  Laws.nonpawn_strategy_complete(
                    rest, 1n,
                    squares, squares,
                    kind,
                    Resource.BlackValue{
                      wk, bk, dest,
                      next_clock},
                    {==}, same, major,
                    no_pawn, child)))
        case Inr{later}:
          +reset = U32.is_eq(kind,
            4) && U32.is_ne(pc,
              dest)
          or_right(
            Rules.move_to(kind,
              Rules.State{wk, bk,
                pc, 0},
              Rules.State{wk, bk,
                dest, 1}) &&
            Minimax.win(rest, 1n,
              squares, squares,
              Minimax.Value{kind,
                Rules.State{wk,
                  bk, dest, 1},
                Bool.pick(Nat,
                  reset, 0n,
                  1n+clock)}),
            Minimax.win(1n+rest,
              0n, tail, squares,
              Minimax.Piece{kind,
                wk, bk, pc,
                clock}),
            Laws.nonpawn_strategy_complete(
              1n+rest, 0n,
              tail, squares, kind,
              Resource.Piece{wk,
                bk, pc, clock},
              {==}, same, major,
              no_pawn, later))
    case 1n++rest 0n Nil{}
         Resource.BlackAll{wk,
           bk, pc, clock,
           all_so_far}:
      match evidence:
        case (all_yes, empty):
          wdl_truth_to_laws_truth(
            all_so_far, all_yes)
    case 1n++rest 0n +dest <> tail
         Resource.BlackAll{+wk,
           +bk, +pc, +clock,
           +all_so_far}:
      match evidence:
        case (all_yes, (head, later)):
          +legal = Rules.black_move(
            kind, wk, bk, pc,
            dest)
          +safe = U32.is_ne(dest,
            pc)
          +child = Minimax.win(rest,
            1n, squares, squares,
            Minimax.Value{kind,
              Rules.State{wk, dest,
                pc, 0},
              1n+clock})
          +implies =
            Bool.not(legal) ||
            (safe && child)
          +updated = all_so_far &&
            implies
          +implication_yes =
            guarded_or_from_implies(
              legal,
              safe && child,
              legal_yes =>
                nonpawn_blackall_complete_head(
                  rest, clock, squares,
                  kind, wk, bk, pc,
                  dest,
                  head(laws_truth_to_wdl_truth(
                    legal, legal_yes)),
                  child_strategy =>
                    Laws.nonpawn_strategy_complete(
                      rest, 1n,
                      squares, squares,
                      kind,
                      Resource.WhiteValue{
                        wk, dest, pc,
                        1n+clock},
                      {==}, same,
                      major, no_pawn,
                      child_strategy)))
          Laws.nonpawn_strategy_complete(
            1n+rest, 0n,
            tail, squares, kind,
            Resource.BlackAll{
              wk, bk, pc, clock,
              updated},
            {==}, same, major,
            no_pawn,
            (laws_truth_to_wdl_truth(
               updated,
               and_intro(all_so_far,
                 implies,
                 wdl_truth_to_laws_truth(
                   all_so_far,
                   all_yes),
                 implication_yes)),
             later))
    case 1n++rest 1n _
         Resource.WhiteValue{+wk,
           +bk, +pc, +clock}:
      match evidence:
        case (valid_yes,
            (before_yes, choice)):
          match choice:
            case Inl{king_strategy}:
              +king = Minimax.win(
                1n+rest, 0n,
                squares, squares,
                Minimax.King{kind,
                  wk, bk, pc,
                  clock})
              +piece = Minimax.win(
                1n+rest, 0n,
                squares, squares,
                Minimax.Piece{kind,
                  wk, bk, pc,
                  clock})
              nonpawn_white_value_complete_finish(
                rest, clock, squares,
                kind, wk, bk, pc,
                valid_yes,
                before_yes, major,
                or_left(king, piece,
                  Laws.nonpawn_strategy_complete(
                    1n+rest, 0n,
                    squares, squares,
                    kind,
                    Resource.King{wk,
                      bk, pc, clock},
                    {==}, same,
                    major, no_pawn,
                    king_strategy)))
            case Inr{piece_strategy}:
              +king = Minimax.win(
                1n+rest, 0n,
                squares, squares,
                Minimax.King{kind,
                  wk, bk, pc,
                  clock})
              +piece = Minimax.win(
                1n+rest, 0n,
                squares, squares,
                Minimax.Piece{kind,
                  wk, bk, pc,
                  clock})
              nonpawn_white_value_complete_finish(
                rest, clock, squares,
                kind, wk, bk, pc,
                valid_yes,
                before_yes, major,
                or_right(king, piece,
                  Laws.nonpawn_strategy_complete(
                    1n+rest, 0n,
                    squares, squares,
                    kind,
                    Resource.Piece{wk,
                      bk, pc, clock},
                    {==}, same,
                    major, no_pawn,
                    piece_strategy)))
    case 1n++rest 1n _
         Resource.BlackValue{+wk,
           +bk, +pc, +clock}:
      match evidence:
        case (valid_yes, outcome):
          match outcome:
            case Inl{mate_strategy}:
              +valid = Rules.valid(
                kind, Rules.State{
                  wk, bk, pc, 1})
              +has = Minimax.has_move(
                squares, kind,
                wk, bk, pc, False{})
              +attack = Rules.attacks(
                kind, pc, bk, wk)
              +mate = Bool.not(has) &&
                attack
              +before = Nat.is_lt(
                clock, 100n)
              +all = Minimax.win(
                1n+rest, 0n,
                squares, squares,
                Minimax.BlackAll{kind,
                  wk, bk, pc, clock,
                  True{}})
              +continuation =
                (before && has) && all
              mate_yes =
                Laws.minimax_mate_complete(
                  squares, kind,
                  wk, bk, pc,
                  mate_strategy)
              nonpawn_black_value_complete_finish(
                rest, clock, squares,
                kind, wk, bk, pc,
                valid_yes, major,
                or_left(mate,
                  continuation,
                  and_right(valid,
                    mate, mate_yes)))
            case Inr{next}:
              match next:
                case (before_yes,
                    (witness,
                      all_strategy)):
                  +has = Minimax.has_move(
                    squares, kind,
                    wk, bk, pc,
                    False{})
                  +before = Nat.is_lt(
                    clock, 100n)
                  +all = Minimax.win(
                    1n+rest, 0n,
                    squares, squares,
                    Minimax.BlackAll{kind,
                      wk, bk, pc,
                      clock, True{}})
                  +mate = Bool.not(has) &&
                    Rules.attacks(kind,
                      pc, bk, wk)
                  +first = before && has
                  +continuation =
                    first && all
                  +first_yes = and_intro(
                    before, has,
                    wdl_truth_to_laws_truth(
                      before,
                      before_yes),
                    Laws.minimax_has_move_from_witness(
                      squares, kind,
                      wk, bk, pc,
                      witness))
                  +all_yes =
                    Laws.nonpawn_strategy_complete(
                      1n+rest, 0n,
                      squares, squares,
                      kind,
                      Resource.BlackAll{
                        wk, bk, pc,
                        clock, True{}},
                      {==}, same,
                      major, no_pawn,
                      (Unit{},
                       all_strategy))
                  nonpawn_black_value_complete_finish(
                    rest, clock, squares,
                    kind, wk, bk, pc,
                    valid_yes, major,
                    or_right(mate,
                      continuation,
                      and_intro(first,
                        all,
                        first_yes,
                        all_yes)))
    case fuel 0n candidates
         Resource.WhiteValue{wk,
           bk, pc, clock}:
      Empty.absurd(
        Laws.Truth(Minimax.win(fuel,
          0n, candidates, squares,
          Minimax.Value{kind,
            Rules.State{wk, bk,
              pc, 0}, clock})),
        zero_eq_one_absurd(
          phase_eq))
    case fuel 2n+more candidates
         Resource.WhiteValue{wk,
           bk, pc, clock}:
      Empty.absurd(
        Laws.Truth(Minimax.win(fuel,
          2n+more, candidates,
          squares,
          Minimax.Value{kind,
            Rules.State{wk, bk,
              pc, 0}, clock})),
        two_plus_nat_eq_one_absurd(
          more, phase_eq))
    case fuel 0n candidates
         Resource.BlackValue{wk,
           bk, pc, clock}:
      Empty.absurd(
        Laws.Truth(Minimax.win(fuel,
          0n, candidates, squares,
          Minimax.Value{kind,
            Rules.State{wk, bk,
              pc, 1}, clock})),
        zero_eq_one_absurd(
          phase_eq))
    case fuel 2n+more candidates
         Resource.BlackValue{wk,
           bk, pc, clock}:
      Empty.absurd(
        Laws.Truth(Minimax.win(fuel,
          2n+more, candidates,
          squares,
          Minimax.Value{kind,
            Rules.State{wk, bk,
              pc, 1}, clock})),
        two_plus_nat_eq_one_absurd(
          more, phase_eq))
    case fuel 1n+more candidates
         Resource.King{wk, bk,
           pc, clock}:
      Empty.absurd(
        Laws.Truth(Minimax.win(fuel,
          1n+more, candidates,
          squares,
          Minimax.King{kind,
            wk, bk, pc, clock})),
        positive_nat_eq_zero_absurd(
          more, phase_eq))
    case fuel 1n+more candidates
         Resource.Piece{wk, bk,
           pc, clock}:
      Empty.absurd(
        Laws.Truth(Minimax.win(fuel,
          1n+more, candidates,
          squares,
          Minimax.Piece{kind,
            wk, bk, pc, clock})),
        positive_nat_eq_zero_absurd(
          more, phase_eq))
    case fuel 1n+more candidates
         Resource.BlackAll{wk,
           bk, pc, clock,
           all_so_far}:
      Empty.absurd(
        Laws.Truth(Minimax.win(fuel,
          1n+more, candidates,
          squares,
          Minimax.BlackAll{kind,
            wk, bk, pc, clock,
            all_so_far})),
        positive_nat_eq_zero_absurd(
          more, phase_eq))

def Laws.nonpawn_white_value_strategy_sound(
  fuel, clock, squares, kind,
  wk, bk, pc, same,
  no_pawn, yes):
  Laws.nonpawn_strategy_sound(
    fuel, 1n, squares, squares,
    kind,
    Resource.WhiteValue{wk,
      bk, pc, clock},
    {==}, same, no_pawn, yes)

def Laws.nonpawn_white_value_strategy_complete(
  fuel, clock, squares, kind,
  wk, bk, pc, same, major,
  no_pawn, evidence):
  Laws.nonpawn_strategy_complete(
    fuel, 1n, squares, squares,
    kind,
    Resource.WhiteValue{wk,
      bk, pc, clock},
    {==}, same, major,
    no_pawn, evidence)

def Laws.nonpawn_black_value_strategy_sound(
  fuel, clock, squares, kind,
  wk, bk, pc, same,
  no_pawn, yes):
  Laws.nonpawn_strategy_sound(
    fuel, 1n, squares, squares,
    kind,
    Resource.BlackValue{wk,
      bk, pc, clock},
    {==}, same, no_pawn, yes)

def Laws.nonpawn_black_value_strategy_complete(
  fuel, clock, squares, kind,
  wk, bk, pc, same, major,
  no_pawn, evidence):
  Laws.nonpawn_strategy_complete(
    fuel, 1n, squares, squares,
    kind,
    Resource.BlackValue{wk,
      bk, pc, clock},
    {==}, same, major,
    no_pawn, evidence)

def Laws.promoted_strategy_sound(
  squares, kind, wk, bk, pc,
  same, no_pawn, yes):
  fuel => fuel_is_100 =>
    Laws.nonpawn_black_value_strategy_sound(
      fuel, 0n, squares,
      kind, wk, bk, pc,
      same, no_pawn,
      equality_cast(Nat,
        value => Laws.Truth(
          Minimax.value(value, 0n,
            squares, kind,
            Rules.State{wk,
              bk, pc, 1})),
        100n, fuel,
        Equal.sym(Nat,
          fuel, 100n,
          fuel_is_100),
        yes))

def Laws.promoted_strategy_complete_at(
  fuel, squares, kind,
  wk, bk, pc, fuel_is_100,
  same, major, no_pawn,
  evidence):
  equality_cast(Nat,
    value => Laws.Truth(
      Minimax.value(value, 0n,
        squares, kind,
        Rules.State{wk,
          bk, pc, 1})),
    fuel, 100n,
    Laws.nat_equality_reflects_identity(
      fuel, 100n,
      fuel_is_100),
    Laws.nonpawn_black_value_strategy_complete(
      fuel, 0n, squares,
      kind, wk, bk, pc,
      same, major, no_pawn,
      evidence(fuel,
        Laws.nat_equality_reflects_identity(
          fuel, 100n,
          fuel_is_100))))

def pawn_blackall_sound_finish(
  +pushes: Nat, +clock_rest: Nat,
  +tail: List<&2, U32>,
  +squares: List<&2, U32>,
  +dest: U32, +wk: U32,
  +bk: U32, +pc: U32,
  +all_so_far: Bool,
  later: Resource.PawnEvidence(
    pushes, 1n+clock_rest,
    0n, tail, squares,
    Resource.PawnBlackAll{wk, bk,
      pc, all_so_far &&
        (Bool.not(Rules.black_move(
          4, wk, bk, pc,
          dest)) ||
         (U32.is_ne(dest, pc) &&
          Exact.win(pushes,
            clock_rest, 1n,
            squares, squares,
            Exact.Value{4,
              Rules.State{wk,
                dest, pc, 0}})))})
  child_sound: Laws.Truth(Exact.win(
    pushes, clock_rest, 1n,
    squares, squares,
    Exact.Value{4,
      Rules.State{wk, dest,
        pc, 0}})) ->
    Resource.Pawn(pushes,
      clock_rest, squares,
      Rules.State{wk, dest,
        pc, 0})) ->
  Resource.PawnEvidence(pushes,
    1n+clock_rest, 0n,
    dest <> tail, squares,
    Resource.PawnBlackAll{wk,
      bk, pc, all_so_far}):
  match later:
    case (+updated_yes, rest_all):
      +legal = Rules.black_move(
        4, wk, bk, pc,
        dest)
      +safe = U32.is_ne(dest,
        pc)
      +child = Exact.win(pushes,
        clock_rest, 1n,
        squares, squares,
        Exact.Value{4,
          Rules.State{wk, dest,
            pc, 0}})
      +implies = Bool.not(legal) ||
        (safe && child)
      +updated = all_so_far &&
        implies
      +guarded = and_right(
        all_so_far, implies,
        wdl_truth_to_laws_truth(
          updated, updated_yes))
      (laws_truth_to_wdl_truth(
         all_so_far,
         and_left(all_so_far,
           implies,
           wdl_truth_to_laws_truth(
             updated,
             updated_yes))),
       (legal_yes =>
          +good =
            guarded_or_to_implies(
              legal, safe && child,
              guarded,
              wdl_truth_to_laws_truth(
                legal, legal_yes))
          (laws_truth_to_wdl_truth(
             safe,
             and_left(safe, child,
               good)),
           child_sound(
             and_right(safe, child,
               good))),
        rest_all))

def pawn_blackall_every(
  +pushes: Nat,
  +clock_rest: Nat,
  +squares: List<&2, U32>,
  +wk: U32, +bk: U32,
  +pc: U32,
  evidence: Resource.PawnEvidence(
    pushes, 1n+clock_rest,
    0n, squares, squares,
    Resource.PawnBlackAll{wk, bk,
      pc, True{}})) ->
  Laws.PawnBlackEvery(pushes,
    clock_rest, squares,
    wk, bk, pc):
  match evidence:
    case (true_proof, all):
      all

def Laws.exact_pawn_king_scan_unfold(
  pushes, clock_rest, dest,
  tail, squares, wk, bk, pc):
  match pushes:
    case 0n:
      {==}
    case 1n+rest:
      {==}

def Laws.exact_pawn_blackall_scan_unfold(
  pushes, clock_rest, dest,
  tail, squares, wk, bk, pc,
  all_so_far):
  match pushes:
    case 0n:
      {==}
    case 1n+rest:
      {==}

def Laws.pawn_strategy_sound(
  pushes, remaining, phase,
  candidates, squares,
  task, phase_eq, same, yes):
  match pushes remaining phase
        candidates task:
    case 0n 0n 1n _
         Resource.PawnWhiteValue{wk,
           bk, pc}:
      yes
    case 0n 0n 1n _
         Resource.PawnBlackValue{wk,
           bk, pc}:
      yes
    case 0n 1n++clock_rest 1n _
         Resource.PawnWhiteValue{wk,
           bk, pc}:
      yes
    case 0n 1n++clock_rest 1n _
         Resource.PawnBlackValue{wk,
           bk, pc}:
      yes
    case 1n++push_rest 0n 1n _
         Resource.PawnWhiteValue{wk,
           bk, pc}:
      yes
    case 1n++push_rest 0n 1n _
         Resource.PawnBlackValue{wk,
           bk, pc}:
      Laws.minimax_zero_nonpawn_sound(
        squares, 4, wk, bk, pc,
        0n,
        +dest => bound =>
          Laws.square_list_equals_member_transfer(
            squares, Squares.all6(),
            dest, same,
            Laws.square_list_complete(
              dest, bound)),
        yes)
    case 0n 0n 0n _
         Resource.PawnKing{wk,
           bk, pc}:
      yes
    case 1n+push_rest 0n 0n _
         Resource.PawnKing{wk,
           bk, pc}:
      yes
    case 0n 0n 0n _
         Resource.PawnPiece{wk,
           bk, pc}:
      yes
    case 1n+push_rest 0n 0n _
         Resource.PawnPiece{wk,
           bk, pc}:
      yes
    case 0n 0n 0n _
         Resource.PawnBlackAll{wk,
           bk, pc, all_so_far}:
      yes
    case 1n+push_rest 0n 0n _
         Resource.PawnBlackAll{wk,
           bk, pc, all_so_far}:
      yes
    case 0n 1n++clock_rest 0n
         Nil{} Resource.PawnKing{wk,
           bk, pc}:
      yes
    case 1n+push_rest
         1n++clock_rest 0n
         Nil{} Resource.PawnKing{wk,
           bk, pc}:
      yes
    case pushes 1n++clock_rest 0n
         +dest <> tail
         Resource.PawnKing{+wk,
           +bk, +pc}:
      +legal = Rules.move_to(4,
        Rules.State{wk, bk, pc,
          0},
        Rules.State{dest, bk,
          pc, 1})
      +won = Exact.win(pushes,
        clock_rest, 1n,
        squares, squares,
        Exact.Value{4,
          Rules.State{dest, bk,
            pc, 1}})
      +later = Exact.win(pushes,
        1n+clock_rest, 0n,
        tail, squares,
        Exact.King{4, wk,
          bk, pc})
      +raw = Exact.win(pushes,
        1n+clock_rest, 0n,
        dest <> tail, squares,
        Exact.King{4, wk,
          bk, pc})
      +expanded = (legal && won) ||
        later
      or_cases(
        Resource.PawnEvidence(
          pushes,
          1n+clock_rest, 0n,
          dest <> tail, squares,
          Resource.PawnKing{wk,
            bk, pc}),
        legal && won, later,
        equality_cast(Bool,
          Laws.Truth, raw, expanded,
          Laws.exact_pawn_king_scan_unfold(
            pushes, clock_rest,
            dest, tail, squares,
            wk, bk, pc), yes),
        +head => Inl{(
          laws_truth_to_wdl_truth(
            legal,
            and_left(legal, won,
              head)),
          Laws.pawn_strategy_sound(
            pushes, clock_rest,
            1n, squares, squares,
            Resource.PawnBlackValue{
              dest, bk, pc},
            {==}, same,
            and_right(legal,
              won, head)))},
        rest_yes => Inr{
          Laws.pawn_strategy_sound(
            pushes,
            1n+clock_rest, 0n,
            tail, squares,
            Resource.PawnKing{wk,
              bk, pc},
            {==}, same,
            rest_yes)})
    case 0n 1n++clock_rest 0n
         Nil{} Resource.PawnPiece{
           wk, bk, pc}:
      yes
    case 0n 1n++clock_rest 0n
         +dest <> tail
         Resource.PawnPiece{+wk,
           +bk, +pc}:
      +legal = Rules.move_to(4,
        Rules.State{wk, bk, pc,
          0},
        Rules.State{wk, bk,
          dest, 1})
      +won = Exact.win(0n,
        clock_rest, 1n,
        squares, squares,
        Exact.Value{4,
          Rules.State{wk, bk,
            dest, 1}})
      +later = Exact.win(0n,
        1n+clock_rest, 0n,
        tail, squares,
        Exact.Piece{4, wk,
          bk, pc})
      or_cases(
        Resource.PawnEvidence(0n,
          1n+clock_rest, 0n,
          dest <> tail, squares,
          Resource.PawnPiece{
            wk, bk, pc}),
        legal && won, later,
        yes,
        +head => Inl{(
          laws_truth_to_wdl_truth(
            legal,
            and_left(legal, won,
              head)),
          Laws.pawn_strategy_sound(
            0n, clock_rest, 1n,
            squares, squares,
            Resource.PawnBlackValue{
              wk, bk, dest},
            {==}, same,
            and_right(legal,
              won, head)))},
        rest_yes => Inr{
          Laws.pawn_strategy_sound(
            0n, 1n+clock_rest,
            0n, tail, squares,
            Resource.PawnPiece{
              wk, bk, pc},
            {==}, same,
            rest_yes)})
    case 1n++push_rest
         1n++clock_rest 0n Nil{}
         Resource.PawnPiece{wk,
           bk, pc}:
      yes
    case 1n++push_rest
         1n++clock_rest 0n
         +dest <> tail
         Resource.PawnPiece{+wk,
           +bk, +pc}:
      +legal = Rules.move_to(4,
        Rules.State{wk, bk, pc,
          0},
        Rules.State{wk, bk,
          dest, 1})
      +reset = U32.is_eq(4,
        4) && U32.is_ne(pc,
          dest)
      +pushed = Exact.win(
        push_rest, 100n, 1n,
        squares, squares,
        Exact.Value{4,
          Rules.State{wk, bk,
            dest, 1}})
      +quiet = Exact.win(
        1n+push_rest,
        clock_rest, 1n,
        squares, squares,
        Exact.Value{4,
          Rules.State{wk, bk,
            dest, 1}})
      +picked = Bool.pick(Bool,
        reset, pushed, quiet)
      +later = Exact.win(
        1n+push_rest,
        1n+clock_rest, 0n,
        tail, squares,
        Exact.Piece{4, wk,
          bk, pc})
      or_cases(
        Resource.PawnEvidence(
          1n+push_rest,
          1n+clock_rest, 0n,
          dest <> tail, squares,
          Resource.PawnPiece{
            wk, bk, pc}),
        legal && picked,
        later, yes,
        +head =>
          +legal_yes = and_left(
            legal, picked, head)
          Inl{(
            laws_truth_to_wdl_truth(
              legal, legal_yes),
            Laws.pawn_strategy_sound(
              push_rest, 100n, 1n,
              squares, squares,
              Resource.PawnBlackValue{
                wk, bk, dest},
              {==}, same,
              bool_pick_true_sound(
                reset, pushed, quiet,
                Laws.legal_pawn_piece_move_resets_clock(
                  wk, bk, pc, dest,
                  legal_yes),
                and_right(legal,
                  picked, head))))},
        rest_yes => Inr{
          Laws.pawn_strategy_sound(
            1n+push_rest,
            1n+clock_rest, 0n,
            tail, squares,
            Resource.PawnPiece{
              wk, bk, pc},
            {==}, same,
            rest_yes)})
    case 0n 1n++clock_rest 0n
         Nil{} Resource.PawnBlackAll{
           wk, bk, pc,
           all_so_far}:
      (laws_truth_to_wdl_truth(
        all_so_far, yes),
       Unit{})
    case 1n+push_rest
         1n++clock_rest 0n
         Nil{} Resource.PawnBlackAll{
           wk, bk, pc,
           all_so_far}:
      (laws_truth_to_wdl_truth(
        all_so_far, yes),
       Unit{})
    case pushes 1n++clock_rest 0n
         +dest <> tail
         Resource.PawnBlackAll{+wk,
           +bk, +pc,
           +all_so_far}:
      +legal = Rules.black_move(
        4, wk, bk, pc,
        dest)
      +safe = U32.is_ne(dest,
        pc)
      +child = Exact.win(pushes,
        clock_rest, 1n,
        squares, squares,
        Exact.Value{4,
          Rules.State{wk, dest,
            pc, 0}})
      +implies = Bool.not(legal) ||
        (safe && child)
      +updated = all_so_far &&
        implies
      +raw = Exact.win(pushes,
        1n+clock_rest, 0n,
        dest <> tail, squares,
        Exact.BlackAll{4, wk,
          bk, pc, all_so_far})
      +expanded = Exact.win(pushes,
        1n+clock_rest, 0n,
        tail, squares,
        Exact.BlackAll{4, wk,
          bk, pc, updated})
      pawn_blackall_sound_finish(
        pushes, clock_rest,
        tail, squares, dest,
        wk, bk, pc,
        all_so_far,
        Laws.pawn_strategy_sound(
          pushes,
          1n+clock_rest,
          0n, tail, squares,
          Resource.PawnBlackAll{
            wk, bk, pc,
            updated},
          {==}, same,
          equality_cast(Bool,
            Laws.Truth, raw,
            expanded,
            Laws.exact_pawn_blackall_scan_unfold(
              pushes,
              clock_rest, dest,
              tail, squares,
              wk, bk, pc,
              all_so_far),
            yes)),
        child_yes =>
          Laws.pawn_strategy_sound(
            pushes, clock_rest,
            1n, squares,
            squares,
            Resource.PawnWhiteValue{
              wk, dest, pc},
            {==}, same,
            child_yes))
    case 1n++push_rest
         1n++clock_rest 1n _
         Resource.PawnWhiteValue{
           +wk, +bk, +pc}:
      +valid = Rules.valid(4,
        Rules.State{wk, bk, pc,
          0})
      +bishop = Bool.not(
        U32.is_eq(4, 2))
      +knight = Bool.not(
        U32.is_eq(4, 3))
      +king = Exact.win(
        1n+push_rest,
        1n+clock_rest, 0n,
        squares, squares,
        Exact.King{4, wk,
          bk, pc})
      +piece = Exact.win(
        1n+push_rest,
        1n+clock_rest, 0n,
        squares, squares,
        Exact.Piece{4, wk,
          bk, pc})
      +target = (pc + 8 : U32)
      +qlegal = WDL.promotion(
        wk, bk, pc, 0,
        wk, bk, target)
      +qwin = Minimax.value(100n,
        0n, squares, 0,
        Rules.State{wk, bk,
          target, 1})
      +rlegal = WDL.promotion(
        wk, bk, pc, 1,
        wk, bk, target)
      +rwin = Minimax.value(100n,
        0n, squares, 1,
        Rules.State{wk, bk,
          target, 1})
      +promotion =
        U32.is_eq(4, 4) &&
        ((qlegal && qwin) ||
         (rlegal && rwin))
      +move = king || piece
      +body = move || promotion
      +prefix = (valid && bishop) &&
        knight
      +prefix_yes = and_left(
        prefix, body, yes)
      +valid_yes = and_left(
        valid, bishop,
        and_left(valid && bishop,
          knight, prefix_yes))
      body_yes = and_right(
        prefix, body, yes)
      or_cases(
        Resource.Pawn(1n+push_rest,
          1n+clock_rest, squares,
          Rules.State{wk, bk,
            pc, 0}),
        move, promotion,
        body_yes,
        move_yes =>
          or_cases(
            Resource.Pawn(
              1n+push_rest,
              1n+clock_rest,
              squares,
              Rules.State{wk,
                bk, pc, 0}),
            king, piece,
            move_yes,
            king_yes =>
              (laws_truth_to_wdl_truth(
                 valid, valid_yes),
               Inl{Inl{
                 Laws.pawn_strategy_sound(
                   1n+push_rest,
                   1n+clock_rest,
                   0n, squares,
                   squares,
                   Resource.PawnKing{
                     wk, bk, pc},
                   {==}, same,
                   king_yes)}}),
            piece_yes =>
              (laws_truth_to_wdl_truth(
                 valid, valid_yes),
               Inl{Inr{
                 Laws.pawn_strategy_sound(
                   1n+push_rest,
                   1n+clock_rest,
                   0n, squares,
                   squares,
                   Resource.PawnPiece{
                     wk, bk, pc},
                   {==}, same,
                   piece_yes)}})),
        promo_yes =>
          or_cases(
            Resource.Pawn(
              1n+push_rest,
              1n+clock_rest,
              squares,
              Rules.State{wk,
                bk, pc, 0}),
            qlegal && qwin,
            rlegal && rwin,
            and_right(U32.is_eq(
                4, 4),
              (qlegal && qwin) ||
                (rlegal && rwin),
              promo_yes),
            +queen_yes =>
              (laws_truth_to_wdl_truth(
                 valid, valid_yes),
               Inr{Inl{(
                 laws_truth_to_wdl_truth(
                   qlegal,
                   and_left(qlegal,
                     qwin, queen_yes)),
                 Laws.promoted_strategy_sound(
                   squares, 0,
                   wk, bk, target,
                   same, Unit{},
                   and_right(qlegal,
                     qwin,
                     queen_yes)))}}),
            +rook_yes =>
              (laws_truth_to_wdl_truth(
                 valid, valid_yes),
               Inr{Inr{(
                 laws_truth_to_wdl_truth(
                   rlegal,
                   and_left(rlegal,
                     rwin, rook_yes)),
                 Laws.promoted_strategy_sound(
                   squares, 1,
                   wk, bk, target,
                   same, Unit{},
                   and_right(rlegal,
                     rwin,
                     rook_yes)))}})))
    case 1n++push_rest
         1n++clock_rest 1n _
         Resource.PawnBlackValue{
           +wk, +bk, +pc}:
      +valid = Rules.valid(4,
        Rules.State{wk, bk,
          pc, 1})
      +bishop = Bool.not(
        U32.is_eq(4, 2))
      +knight = Bool.not(
        U32.is_eq(4, 3))
      +has = Minimax.has_move(
        squares, 4, wk,
        bk, pc, False{})
      +attack = Rules.attacks(
        4, pc, bk, wk)
      +mate = Bool.not(has) &&
        attack
      +all = Exact.win(
        1n+push_rest,
        1n+clock_rest, 0n,
        squares, squares,
        Exact.BlackAll{4,
          wk, bk, pc,
          True{}})
      +continue = has && all
      +body = mate || continue
      +prefix = (valid && bishop) &&
        knight
      +prefix_yes = and_left(
        prefix, body, yes)
      +valid_yes = and_left(
        valid, bishop,
        and_left(valid && bishop,
          knight, prefix_yes))
      body_yes = and_right(
        prefix, body, yes)
      or_cases(
        Resource.Pawn(1n+push_rest,
          1n+clock_rest, squares,
          Rules.State{wk, bk,
            pc, 1}),
        mate, continue,
        body_yes,
        mate_yes =>
          (laws_truth_to_wdl_truth(
             valid, valid_yes),
           Inl{
             Laws.minimax_mate_sound(
               squares, 4, wk,
               bk, pc,
               +dest => bound =>
                 Laws.square_list_equals_member_transfer(
                   squares,
                   Squares.all6(),
                   dest, same,
                   Laws.square_list_complete(
                     dest, bound)),
               and_intro(valid,
                 mate, valid_yes,
                 mate_yes))}),
        +next_yes =>
          (laws_truth_to_wdl_truth(
             valid, valid_yes),
           Inr{(
             Laws.minimax_has_move_has_witness(
               squares, 4,
               wk, bk, pc,
               and_left(has, all,
                 next_yes)),
             pawn_blackall_every(
               1n+push_rest,
               clock_rest, squares,
               wk, bk, pc,
               Laws.pawn_strategy_sound(
                 1n+push_rest,
                 1n+clock_rest,
                 0n, squares,
                 squares,
                 Resource.PawnBlackAll{
                   wk, bk, pc,
                   True{}},
                 {==}, same,
                 and_right(has,
                   all,
                   next_yes))))}))
    case pushes remaining 0n
         candidates
         Resource.PawnWhiteValue{
           wk, bk, pc}:
      Empty.absurd(
        Resource.PawnEvidence(pushes,
          remaining, 0n,
          candidates, squares,
          Resource.PawnWhiteValue{
            wk, bk, pc}),
        zero_eq_one_absurd(
          phase_eq))
    case pushes remaining
         2n+more candidates
         Resource.PawnWhiteValue{
           wk, bk, pc}:
      Empty.absurd(
        Resource.PawnEvidence(pushes,
          remaining, 2n+more,
          candidates, squares,
          Resource.PawnWhiteValue{
            wk, bk, pc}),
        two_plus_nat_eq_one_absurd(
          more, phase_eq))
    case pushes remaining 0n
         candidates
         Resource.PawnBlackValue{
           wk, bk, pc}:
      Empty.absurd(
        Resource.PawnEvidence(pushes,
          remaining, 0n,
          candidates, squares,
          Resource.PawnBlackValue{
            wk, bk, pc}),
        zero_eq_one_absurd(
          phase_eq))
    case pushes remaining
         2n+more candidates
         Resource.PawnBlackValue{
           wk, bk, pc}:
      Empty.absurd(
        Resource.PawnEvidence(pushes,
          remaining, 2n+more,
          candidates, squares,
          Resource.PawnBlackValue{
            wk, bk, pc}),
        two_plus_nat_eq_one_absurd(
          more, phase_eq))
    case pushes remaining
         1n+more candidates
         Resource.PawnKing{wk,
           bk, pc}:
      Empty.absurd(
        Resource.PawnEvidence(pushes,
          remaining, 1n+more,
          candidates, squares,
          Resource.PawnKing{wk,
            bk, pc}),
        positive_nat_eq_zero_absurd(
          more, phase_eq))
    case pushes remaining
         1n+more candidates
         Resource.PawnPiece{wk,
           bk, pc}:
      Empty.absurd(
        Resource.PawnEvidence(pushes,
          remaining, 1n+more,
          candidates, squares,
          Resource.PawnPiece{wk,
            bk, pc}),
        positive_nat_eq_zero_absurd(
          more, phase_eq))
    case pushes remaining
         1n+more candidates
         Resource.PawnBlackAll{
           wk, bk, pc,
           all_so_far}:
      Empty.absurd(
        Resource.PawnEvidence(pushes,
          remaining, 1n+more,
          candidates, squares,
          Resource.PawnBlackAll{
            wk, bk, pc,
            all_so_far}),
        positive_nat_eq_zero_absurd(
          more, phase_eq))

def pawn_blackall_complete_head(
  +pushes: Nat, +clock_rest: Nat,
  +squares: List<&2, U32>,
  +wk: U32, +bk: U32,
  +pc: U32, +dest: U32,
  good: WDL.Truth(U32.is_ne(dest,
    pc)) & Resource.Pawn(pushes,
      clock_rest, squares,
      Rules.State{wk, dest,
        pc, 0}),
  child_complete:
    Resource.Pawn(pushes,
      clock_rest, squares,
      Rules.State{wk, dest,
        pc, 0}) ->
    Laws.Truth(Exact.win(pushes,
      clock_rest, 1n, squares,
      squares, Exact.Value{4,
        Rules.State{wk, dest,
          pc, 0}}))) ->
  Laws.Truth(U32.is_ne(dest, pc) &&
    Exact.win(pushes, clock_rest,
      1n, squares, squares,
      Exact.Value{4,
        Rules.State{wk, dest,
          pc, 0}})):
  match good:
    case (safe_yes, strategy):
      and_intro(U32.is_ne(dest, pc),
        Exact.win(pushes,
          clock_rest, 1n,
          squares, squares,
          Exact.Value{4,
            Rules.State{wk, dest,
              pc, 0}}),
        wdl_truth_to_laws_truth(
          U32.is_ne(dest, pc),
          safe_yes),
        child_complete(strategy))

def pawn_prefix_body(
  +valid: Bool, +body: Bool,
  valid_yes: WDL.Truth(valid),
  body_yes: Laws.Truth(body)) ->
  Laws.Truth(((valid &&
    Bool.not(U32.is_eq(4, 2))) &&
    Bool.not(U32.is_eq(4, 3))) &&
    body):
  and_intro((valid &&
      Bool.not(U32.is_eq(4, 2))) &&
      Bool.not(U32.is_eq(4, 3)),
    body,
    and_intro(valid &&
        Bool.not(U32.is_eq(4, 2)),
      Bool.not(U32.is_eq(4, 3)),
      and_intro(valid,
        Bool.not(U32.is_eq(4, 2)),
        wdl_truth_to_laws_truth(
          valid, valid_yes),
        Unit{}),
      Unit{}),
    body_yes)

def pawn_white_complete_move(
  +pushes: Nat, +remaining: Nat,
  +squares: List<&2, U32>,
  +wk: U32, +bk: U32, +pc: U32,
  valid_yes: WDL.Truth(Rules.valid(4,
    Rules.State{wk, bk, pc, 0})),
  move_yes: Laws.Truth(
    Exact.win(pushes, remaining,
      0n, squares, squares,
      Exact.King{4, wk, bk, pc}) ||
    Exact.win(pushes, remaining,
      0n, squares, squares,
      Exact.Piece{4, wk, bk, pc}))) ->
  Laws.Truth(
    ((Rules.valid(4,
      Rules.State{wk, bk, pc, 0}) &&
      Bool.not(U32.is_eq(4, 2))) &&
      Bool.not(U32.is_eq(4, 3))) &&
    ((Exact.win(pushes, remaining,
        0n, squares, squares,
        Exact.King{4, wk, bk, pc}) ||
      Exact.win(pushes, remaining,
        0n, squares, squares,
        Exact.Piece{4, wk, bk, pc})) ||
     (U32.is_eq(4, 4) &&
       ((WDL.promotion(wk, bk, pc,
           0, wk, bk,
           (pc + 8 : U32)) &&
         Minimax.value(100n, 0n,
           squares, 0,
           Rules.State{wk, bk,
             (pc + 8 : U32), 1})) ||
        (WDL.promotion(wk, bk, pc,
           1, wk, bk,
           (pc + 8 : U32)) &&
         Minimax.value(100n, 0n,
           squares, 1,
           Rules.State{wk, bk,
             (pc + 8 : U32), 1})))))):
  +valid = Rules.valid(4,
    Rules.State{wk, bk, pc, 0})
  +king = Exact.win(pushes,
    remaining, 0n, squares,
    squares,
    Exact.King{4, wk, bk, pc})
  +piece = Exact.win(pushes,
    remaining, 0n, squares,
    squares,
    Exact.Piece{4, wk, bk, pc})
  +target = (pc + 8 : U32)
  +promotion = U32.is_eq(4, 4) &&
    ((WDL.promotion(wk, bk, pc,
        0, wk, bk, target) &&
      Minimax.value(100n, 0n,
        squares, 0,
        Rules.State{wk, bk,
          target, 1})) ||
     (WDL.promotion(wk, bk, pc,
        1, wk, bk, target) &&
      Minimax.value(100n, 0n,
        squares, 1,
        Rules.State{wk, bk,
          target, 1})))
  pawn_prefix_body(valid,
    (king || piece) || promotion,
    valid_yes,
    or_left(king || piece,
      promotion, move_yes))

def pawn_white_complete_promotion(
  +pushes: Nat, +remaining: Nat,
  +squares: List<&2, U32>,
  +wk: U32, +bk: U32, +pc: U32,
  valid_yes: WDL.Truth(Rules.valid(4,
    Rules.State{wk, bk, pc, 0})),
  choice:
    Laws.Truth(WDL.promotion(wk,
      bk, pc, 0, wk, bk,
      (pc + 8 : U32)) &&
      Minimax.value(100n, 0n,
        squares, 0,
        Rules.State{wk, bk,
          (pc + 8 : U32), 1})) |
    Laws.Truth(WDL.promotion(wk,
      bk, pc, 1, wk, bk,
      (pc + 8 : U32)) &&
      Minimax.value(100n, 0n,
        squares, 1,
        Rules.State{wk, bk,
          (pc + 8 : U32), 1}))) ->
  Laws.Truth(
    ((Rules.valid(4,
      Rules.State{wk, bk, pc, 0}) &&
      Bool.not(U32.is_eq(4, 2))) &&
      Bool.not(U32.is_eq(4, 3))) &&
    ((Exact.win(pushes, remaining,
        0n, squares, squares,
        Exact.King{4, wk, bk, pc}) ||
      Exact.win(pushes, remaining,
        0n, squares, squares,
        Exact.Piece{4, wk, bk, pc})) ||
     (U32.is_eq(4, 4) &&
       ((WDL.promotion(wk, bk, pc,
           0, wk, bk,
           (pc + 8 : U32)) &&
         Minimax.value(100n, 0n,
           squares, 0,
           Rules.State{wk, bk,
             (pc + 8 : U32), 1})) ||
        (WDL.promotion(wk, bk, pc,
           1, wk, bk,
           (pc + 8 : U32)) &&
         Minimax.value(100n, 0n,
           squares, 1,
           Rules.State{wk, bk,
             (pc + 8 : U32), 1})))))):
  match choice:
    case Inl{queen}:
      +valid = Rules.valid(4,
        Rules.State{wk, bk, pc, 0})
      +qlegal = WDL.promotion(wk,
        bk, pc, 0, wk, bk,
        (pc + 8 : U32))
      +qwin = Minimax.value(100n,
        0n, squares, 0,
        Rules.State{wk, bk,
          (pc + 8 : U32), 1})
      +rlegal = WDL.promotion(wk,
        bk, pc, 1, wk, bk,
        (pc + 8 : U32))
      +rwin = Minimax.value(100n,
        0n, squares, 1,
        Rules.State{wk, bk,
          (pc + 8 : U32), 1})
      +move = Exact.win(pushes,
        remaining, 0n, squares,
        squares,
        Exact.King{4, wk, bk,
          pc}) ||
        Exact.win(pushes,
          remaining, 0n,
          squares, squares,
          Exact.Piece{4, wk,
            bk, pc})
      +promotion = U32.is_eq(4, 4) &&
        ((qlegal && qwin) ||
         (rlegal && rwin))
      pawn_prefix_body(valid,
        move || promotion,
        valid_yes,
        or_right(move, promotion,
          and_intro(U32.is_eq(4, 4),
            (qlegal && qwin) ||
              (rlegal && rwin),
            Unit{},
            or_left(qlegal && qwin,
              rlegal && rwin,
              queen))))
    case Inr{rook}:
      +valid = Rules.valid(4,
        Rules.State{wk, bk, pc, 0})
      +qlegal = WDL.promotion(wk,
        bk, pc, 0, wk, bk,
        (pc + 8 : U32))
      +qwin = Minimax.value(100n,
        0n, squares, 0,
        Rules.State{wk, bk,
          (pc + 8 : U32), 1})
      +rlegal = WDL.promotion(wk,
        bk, pc, 1, wk, bk,
        (pc + 8 : U32))
      +rwin = Minimax.value(100n,
        0n, squares, 1,
        Rules.State{wk, bk,
          (pc + 8 : U32), 1})
      +move = Exact.win(pushes,
        remaining, 0n, squares,
        squares,
        Exact.King{4, wk, bk,
          pc}) ||
        Exact.win(pushes,
          remaining, 0n,
          squares, squares,
          Exact.Piece{4, wk,
            bk, pc})
      +promotion = U32.is_eq(4, 4) &&
        ((qlegal && qwin) ||
         (rlegal && rwin))
      pawn_prefix_body(valid,
        move || promotion,
        valid_yes,
        or_right(move, promotion,
          and_intro(U32.is_eq(4, 4),
            (qlegal && qwin) ||
              (rlegal && rwin),
            Unit{},
            or_right(qlegal && qwin,
              rlegal && rwin,
              rook))))

def pawn_black_complete_mate(
  +pushes: Nat, +remaining: Nat,
  +squares: List<&2, U32>,
  +wk: U32, +bk: U32, +pc: U32,
  valid_yes: WDL.Truth(Rules.valid(4,
    Rules.State{wk, bk, pc, 1})),
  mate_yes: Laws.Truth(
    Rules.valid(4,
      Rules.State{wk, bk, pc, 1}) &&
    (Bool.not(Minimax.has_move(
       squares, 4, wk, bk,
       pc, False{})) &&
     Rules.attacks(4, pc, bk,
       wk)))) ->
  Laws.Truth(
    ((Rules.valid(4,
      Rules.State{wk, bk, pc, 1}) &&
      Bool.not(U32.is_eq(4, 2))) &&
      Bool.not(U32.is_eq(4, 3))) &&
    ((Bool.not(Minimax.has_move(
        squares, 4, wk, bk,
        pc, False{})) &&
      Rules.attacks(4, pc, bk,
        wk)) ||
     (Minimax.has_move(squares, 4,
        wk, bk, pc, False{}) &&
      Exact.win(pushes,
        remaining, 0n,
        squares, squares,
        Exact.BlackAll{4,
          wk, bk, pc,
          True{}})))):
  +valid = Rules.valid(4,
    Rules.State{wk, bk, pc, 1})
  +has = Minimax.has_move(squares,
    4, wk, bk, pc, False{})
  +attack = Rules.attacks(4,
    pc, bk, wk)
  +mate = Bool.not(has) && attack
  +all = Exact.win(pushes,
    remaining, 0n,
    squares, squares,
    Exact.BlackAll{4, wk, bk,
      pc, True{}})
  pawn_prefix_body(valid,
    mate || (has && all),
    valid_yes,
    or_left(mate, has && all,
      and_right(valid,
        mate, mate_yes)))

def pawn_black_complete_continue(
  +pushes: Nat, +remaining: Nat,
  +squares: List<&2, U32>,
  +wk: U32, +bk: U32, +pc: U32,
  valid_yes: WDL.Truth(Rules.valid(4,
    Rules.State{wk, bk, pc, 1})),
  has_yes: Laws.Truth(
    Minimax.has_move(squares, 4,
      wk, bk, pc, False{})),
  all_yes: Laws.Truth(
    Exact.win(pushes,
      remaining, 0n,
      squares, squares,
      Exact.BlackAll{4,
        wk, bk, pc,
        True{}}))) ->
  Laws.Truth(
    ((Rules.valid(4,
      Rules.State{wk, bk, pc, 1}) &&
      Bool.not(U32.is_eq(4, 2))) &&
      Bool.not(U32.is_eq(4, 3))) &&
    ((Bool.not(Minimax.has_move(
        squares, 4, wk, bk,
        pc, False{})) &&
      Rules.attacks(4, pc, bk,
        wk)) ||
     (Minimax.has_move(squares, 4,
        wk, bk, pc, False{}) &&
      Exact.win(pushes,
        remaining, 0n,
        squares, squares,
        Exact.BlackAll{4,
          wk, bk, pc,
          True{}})))):
  +valid = Rules.valid(4,
    Rules.State{wk, bk, pc, 1})
  +has = Minimax.has_move(squares,
    4, wk, bk, pc, False{})
  +attack = Rules.attacks(4,
    pc, bk, wk)
  +mate = Bool.not(has) && attack
  +all = Exact.win(pushes,
    remaining, 0n,
    squares, squares,
    Exact.BlackAll{4, wk, bk,
      pc, True{}})
  pawn_prefix_body(valid,
    mate || (has && all),
    valid_yes,
    or_right(mate, has && all,
      and_intro(has, all,
        has_yes, all_yes)))

def Laws.pawn_strategy_complete(
  pushes, remaining, phase,
  candidates, squares,
  task, phase_eq, same,
  evidence):
  match pushes remaining phase
        candidates task:
    case 0n 0n 1n _
         Resource.PawnWhiteValue{wk,
           bk, pc}:
      match evidence:
    case 0n 0n 1n _
         Resource.PawnBlackValue{wk,
           bk, pc}:
      match evidence:
    case 0n 1n+clock_rest 1n _
         Resource.PawnWhiteValue{wk,
           bk, pc}:
      match evidence:
    case 0n 1n+clock_rest 1n _
         Resource.PawnBlackValue{wk,
           bk, pc}:
      match evidence:
    case 1n+push_rest 0n 1n _
         Resource.PawnWhiteValue{wk,
           bk, pc}:
      match evidence:
    case 1n+push_rest 0n 1n _
         Resource.PawnBlackValue{wk,
           bk, pc}:
      Laws.minimax_zero_nonpawn_complete(
        squares, 4, wk, bk, pc,
        0n, Unit{}, evidence)
    case 0n 0n 0n _
         Resource.PawnKing{wk,
           bk, pc}:
      match evidence:
    case 1n+push_rest 0n 0n _
         Resource.PawnKing{wk,
           bk, pc}:
      match evidence:
    case 0n 0n 0n _
         Resource.PawnPiece{wk,
           bk, pc}:
      match evidence:
    case 1n+push_rest 0n 0n _
         Resource.PawnPiece{wk,
           bk, pc}:
      match evidence:
    case 0n 0n 0n _
         Resource.PawnBlackAll{wk,
           bk, pc, all_so_far}:
      match evidence:
    case 1n+push_rest 0n 0n _
         Resource.PawnBlackAll{wk,
           bk, pc, all_so_far}:
      match evidence:
    case 0n 1n+clock_rest 0n
         Nil{} Resource.PawnKing{wk,
           bk, pc}:
      match evidence:
    case 1n+push_rest
         1n+clock_rest 0n
         Nil{} Resource.PawnKing{wk,
           bk, pc}:
      match evidence:
    case pushes 1n++clock_rest 0n
         +dest <> tail
         Resource.PawnKing{+wk,
           +bk, +pc}:
      match evidence:
        case Inl{head}:
          match head:
            case (legal_yes, child):
              +legal = Rules.move_to(4,
                Rules.State{wk, bk,
                  pc, 0},
                Rules.State{dest, bk,
                  pc, 1})
              +won = Exact.win(pushes,
                clock_rest, 1n,
                squares, squares,
                Exact.Value{4,
                  Rules.State{dest,
                    bk, pc, 1}})
              +later = Exact.win(pushes,
                1n+clock_rest, 0n,
                tail, squares,
                Exact.King{4,
                  wk, bk, pc})
              +raw = Exact.win(pushes,
                1n+clock_rest, 0n,
                dest <> tail,
                squares,
                Exact.King{4,
                  wk, bk, pc})
              equality_cast(Bool,
                Laws.Truth,
                (legal && won) || later,
                raw,
                Equal.sym(Bool, raw,
                  (legal && won) || later,
                  Laws.exact_pawn_king_scan_unfold(
                    pushes, clock_rest,
                    dest, tail, squares,
                    wk, bk, pc)),
                or_left(legal && won,
                  later,
                  and_intro(legal,
                    won,
                    wdl_truth_to_laws_truth(
                      legal, legal_yes),
                    Laws.pawn_strategy_complete(
                      pushes, clock_rest,
                      1n, squares, squares,
                      Resource.PawnBlackValue{
                        dest, bk, pc},
                      {==}, same, child))))
        case Inr{later_evidence}:
          +legal = Rules.move_to(4,
            Rules.State{wk, bk, pc, 0},
            Rules.State{dest, bk, pc, 1})
          +won = Exact.win(pushes,
            clock_rest, 1n, squares,
            squares, Exact.Value{4,
              Rules.State{dest, bk,
                pc, 1}})
          +later = Exact.win(pushes,
            1n+clock_rest, 0n,
            tail, squares,
            Exact.King{4,
              wk, bk, pc})
          +raw = Exact.win(pushes,
            1n+clock_rest, 0n,
            dest <> tail, squares,
            Exact.King{4,
              wk, bk, pc})
          equality_cast(Bool,
            Laws.Truth,
            (legal && won) || later,
            raw,
            Equal.sym(Bool, raw,
              (legal && won) || later,
              Laws.exact_pawn_king_scan_unfold(
                pushes, clock_rest,
                dest, tail, squares,
                wk, bk, pc)),
            or_right(legal && won,
              later,
              Laws.pawn_strategy_complete(
                pushes,
                1n+clock_rest, 0n,
                tail, squares,
                Resource.PawnKing{
                  wk, bk, pc},
                {==}, same,
                later_evidence)))
    case 0n 1n++clock_rest 0n
         Nil{} Resource.PawnPiece{wk,
           bk, pc}:
      match evidence:
    case 0n 1n++clock_rest 0n
         +dest <> tail
         Resource.PawnPiece{+wk,
           +bk, +pc}:
      match evidence:
        case Inl{head}:
          match head:
            case (legal_yes, child):
              +legal = Rules.move_to(4,
                Rules.State{wk, bk,
                  pc, 0},
                Rules.State{wk, bk,
                  dest, 1})
              +won = Exact.win(0n,
                clock_rest, 1n,
                squares, squares,
                Exact.Value{4,
                  Rules.State{wk,
                    bk, dest, 1}})
              +later = Exact.win(0n,
                1n+clock_rest, 0n,
                tail, squares,
                Exact.Piece{4,
                  wk, bk, pc})
              or_left(legal && won,
                later,
                and_intro(legal, won,
                  wdl_truth_to_laws_truth(
                    legal, legal_yes),
                  Laws.pawn_strategy_complete(
                    0n, clock_rest, 1n,
                    squares, squares,
                    Resource.PawnBlackValue{
                      wk, bk, dest},
                    {==}, same, child)))
        case Inr{later_evidence}:
          +legal = Rules.move_to(4,
            Rules.State{wk, bk, pc, 0},
            Rules.State{wk, bk, dest, 1})
          +won = Exact.win(0n,
            clock_rest, 1n,
            squares, squares,
            Exact.Value{4,
              Rules.State{wk,
                bk, dest, 1}})
          +later = Exact.win(0n,
            1n+clock_rest, 0n,
            tail, squares,
            Exact.Piece{4,
              wk, bk, pc})
          or_right(legal && won,
            later,
            Laws.pawn_strategy_complete(
              0n, 1n+clock_rest,
              0n, tail, squares,
              Resource.PawnPiece{
                wk, bk, pc},
              {==}, same,
              later_evidence))
    case 1n++push_rest
         1n++clock_rest 0n Nil{}
         Resource.PawnPiece{wk,
           bk, pc}:
      match evidence:
    case 1n++push_rest
         1n++clock_rest 0n
         +dest <> tail
         Resource.PawnPiece{+wk,
           +bk, +pc}:
      match evidence:
        case Inl{head}:
          match head:
            case (legal_yes, child):
              +legal = Rules.move_to(4,
                Rules.State{wk, bk,
                  pc, 0},
                Rules.State{wk, bk,
                  dest, 1})
              +reset = U32.is_eq(4, 4) &&
                U32.is_ne(pc, dest)
              +pushed = Exact.win(
                push_rest, 100n, 1n,
                squares, squares,
                Exact.Value{4,
                  Rules.State{wk,
                    bk, dest, 1}})
              +quiet = Exact.win(
                1n+push_rest,
                clock_rest, 1n,
                squares, squares,
                Exact.Value{4,
                  Rules.State{wk,
                    bk, dest, 1}})
              +picked = Bool.pick(Bool,
                reset, pushed, quiet)
              +later = Exact.win(
                1n+push_rest,
                1n+clock_rest, 0n,
                tail, squares,
                Exact.Piece{4,
                  wk, bk, pc})
              +move_yes =
                wdl_truth_to_laws_truth(
                  legal, legal_yes)
              or_left(legal && picked,
                later,
                and_intro(legal,
                  picked, move_yes,
                  bool_pick_true_complete(
                    reset, pushed,
                    quiet,
                    Laws.legal_pawn_piece_move_resets_clock(
                      wk, bk, pc,
                      dest, move_yes),
                    Laws.pawn_strategy_complete(
                      push_rest, 100n,
                      1n, squares,
                      squares,
                      Resource.PawnBlackValue{
                        wk, bk, dest},
                      {==}, same,
                      child))))
        case Inr{later_evidence}:
          +legal = Rules.move_to(4,
            Rules.State{wk, bk, pc, 0},
            Rules.State{wk, bk, dest, 1})
          +reset = U32.is_eq(4, 4) &&
            U32.is_ne(pc, dest)
          +pushed = Exact.win(
            push_rest, 100n, 1n,
            squares, squares,
            Exact.Value{4,
              Rules.State{wk,
                bk, dest, 1}})
          +quiet = Exact.win(
            1n+push_rest,
            clock_rest, 1n,
            squares, squares,
            Exact.Value{4,
              Rules.State{wk,
                bk, dest, 1}})
          +picked = Bool.pick(Bool,
            reset, pushed, quiet)
          +later = Exact.win(
            1n+push_rest,
            1n+clock_rest, 0n,
            tail, squares,
            Exact.Piece{4,
              wk, bk, pc})
          or_right(legal && picked,
            later,
            Laws.pawn_strategy_complete(
              1n+push_rest,
              1n+clock_rest, 0n,
              tail, squares,
              Resource.PawnPiece{
                wk, bk, pc},
              {==}, same,
              later_evidence))
    case 0n 1n++clock_rest 0n
         Nil{} Resource.PawnBlackAll{
           wk, bk, pc,
           all_so_far}:
      match evidence:
        case (all_yes, empty):
          wdl_truth_to_laws_truth(
            all_so_far, all_yes)
    case 1n+push_rest
         1n++clock_rest 0n
         Nil{} Resource.PawnBlackAll{
           wk, bk, pc,
           all_so_far}:
      match evidence:
        case (all_yes, empty):
          wdl_truth_to_laws_truth(
            all_so_far, all_yes)
    case pushes 1n++clock_rest 0n
         +dest <> tail
         Resource.PawnBlackAll{+wk,
           +bk, +pc,
           +all_so_far}:
      match evidence:
        case (all_yes, (head, later)):
          +legal = Rules.black_move(4,
            wk, bk, pc, dest)
          +safe = U32.is_ne(dest, pc)
          +child = Exact.win(pushes,
            clock_rest, 1n,
            squares, squares,
            Exact.Value{4,
              Rules.State{wk, dest,
                pc, 0}})
          +implies = Bool.not(legal) ||
            (safe && child)
          +updated = all_so_far &&
            implies
          +raw = Exact.win(pushes,
            1n+clock_rest, 0n,
            dest <> tail, squares,
            Exact.BlackAll{4,
              wk, bk, pc,
              all_so_far})
          +expanded = Exact.win(pushes,
            1n+clock_rest, 0n,
            tail, squares,
            Exact.BlackAll{4,
              wk, bk, pc,
              updated})
          +implies_yes =
            guarded_or_from_implies(
              legal, safe && child,
              legal_yes =>
                pawn_blackall_complete_head(
                  pushes, clock_rest,
                  squares, wk, bk,
                  pc, dest,
                  head(laws_truth_to_wdl_truth(
                    legal, legal_yes)),
                  child_strategy =>
                    Laws.pawn_strategy_complete(
                      pushes,
                      clock_rest, 1n,
                      squares, squares,
                      Resource.PawnWhiteValue{
                        wk, dest, pc},
                      {==}, same,
                      child_strategy)))
          equality_cast(Bool,
            Laws.Truth, expanded,
            raw,
            Equal.sym(Bool, raw,
              expanded,
              Laws.exact_pawn_blackall_scan_unfold(
                pushes,
                clock_rest, dest,
                tail, squares,
                wk, bk, pc,
                all_so_far)),
            Laws.pawn_strategy_complete(
              pushes,
              1n+clock_rest, 0n,
              tail, squares,
              Resource.PawnBlackAll{
                wk, bk, pc,
                updated},
              {==}, same,
              (laws_truth_to_wdl_truth(
                 updated,
                 and_intro(all_so_far,
                   implies,
                   wdl_truth_to_laws_truth(
                     all_so_far,
                     all_yes),
                   implies_yes)),
               later)))
    case 1n++push_rest
         1n++clock_rest 1n _
         Resource.PawnWhiteValue{
           +wk, +bk, +pc}:
      match evidence:
        case (valid_yes, choice):
          match choice:
            case Inl{move}:
              match move:
                case Inl{king}:
                  pawn_white_complete_move(
                    1n+push_rest,
                    1n+clock_rest,
                    squares, wk,
                    bk, pc,
                    valid_yes,
                    or_left(
                      Exact.win(
                        1n+push_rest,
                        1n+clock_rest,
                        0n, squares,
                        squares,
                        Exact.King{4,
                          wk, bk, pc}),
                      Exact.win(
                        1n+push_rest,
                        1n+clock_rest,
                        0n, squares,
                        squares,
                        Exact.Piece{4,
                          wk, bk, pc}),
                      Laws.pawn_strategy_complete(
                        1n+push_rest,
                        1n+clock_rest,
                        0n, squares,
                        squares,
                        Resource.PawnKing{
                          wk, bk, pc},
                        {==}, same,
                        king)))
                case Inr{piece}:
                  pawn_white_complete_move(
                    1n+push_rest,
                    1n+clock_rest,
                    squares, wk,
                    bk, pc,
                    valid_yes,
                    or_right(
                      Exact.win(
                        1n+push_rest,
                        1n+clock_rest,
                        0n, squares,
                        squares,
                        Exact.King{4,
                          wk, bk, pc}),
                      Exact.win(
                        1n+push_rest,
                        1n+clock_rest,
                        0n, squares,
                        squares,
                        Exact.Piece{4,
                          wk, bk, pc}),
                      Laws.pawn_strategy_complete(
                        1n+push_rest,
                        1n+clock_rest,
                        0n, squares,
                        squares,
                        Resource.PawnPiece{
                          wk, bk, pc},
                        {==}, same,
                        piece)))
            case Inr{promotion}:
              match promotion:
                case Inl{queen}:
                  match queen:
                    case (legal_yes,
                        promoted):
                      pawn_white_complete_promotion(
                        1n+push_rest,
                        1n+clock_rest,
                        squares, wk,
                        bk, pc,
                        valid_yes,
                        Inl{and_intro(
                          WDL.promotion(wk,
                            bk, pc, 0,
                            wk, bk,
                            (pc + 8 : U32)),
                          Minimax.value(100n,
                            0n, squares, 0,
                            Rules.State{wk,
                              bk,
                              (pc + 8 : U32),
                              1}),
                          wdl_truth_to_laws_truth(
                            WDL.promotion(wk,
                              bk, pc, 0,
                              wk, bk,
                              (pc + 8 : U32)),
                            legal_yes),
                          Laws.promoted_strategy_complete_at(
                            100n, squares,
                            0, wk, bk,
                            (pc + 8 : U32),
                            Unit{}, same,
                            Unit{}, Unit{},
                            promoted))})
                case Inr{rook}:
                  match rook:
                    case (legal_yes,
                        promoted):
                      pawn_white_complete_promotion(
                        1n+push_rest,
                        1n+clock_rest,
                        squares, wk,
                        bk, pc,
                        valid_yes,
                        Inr{and_intro(
                          WDL.promotion(wk,
                            bk, pc, 1,
                            wk, bk,
                            (pc + 8 : U32)),
                          Minimax.value(100n,
                            0n, squares, 1,
                            Rules.State{wk,
                              bk,
                              (pc + 8 : U32),
                              1}),
                          wdl_truth_to_laws_truth(
                            WDL.promotion(wk,
                              bk, pc, 1,
                              wk, bk,
                              (pc + 8 : U32)),
                            legal_yes),
                          Laws.promoted_strategy_complete_at(
                            100n, squares,
                            1, wk, bk,
                            (pc + 8 : U32),
                            Unit{}, same,
                            Unit{}, Unit{},
                            promoted))})
    case 1n++push_rest
         1n++clock_rest 1n _
         Resource.PawnBlackValue{
           +wk, +bk, +pc}:
      match evidence:
        case (valid_yes, outcome):
          match outcome:
            case Inl{mate}:
              pawn_black_complete_mate(
                1n+push_rest,
                1n+clock_rest,
                squares, wk,
                bk, pc,
                valid_yes,
                Laws.minimax_mate_complete(
                  squares, 4,
                  wk, bk, pc,
                  mate))
            case Inr{continuation}:
              match continuation:
                case (has_witness,
                    all_evidence):
                  pawn_black_complete_continue(
                    1n+push_rest,
                    1n+clock_rest,
                    squares, wk,
                    bk, pc,
                    valid_yes,
                    Laws.minimax_has_move_from_witness(
                      squares, 4,
                      wk, bk, pc,
                      has_witness),
                    Laws.pawn_strategy_complete(
                      1n+push_rest,
                      1n+clock_rest,
                      0n, squares,
                      squares,
                      Resource.PawnBlackAll{
                        wk, bk, pc,
                        True{}},
                      {==}, same,
                      (Unit{},
                       all_evidence)))
    case pushes remaining 0n
         candidates
         Resource.PawnWhiteValue{
           wk, bk, pc}:
      Empty.absurd(
        Laws.Truth(Exact.win(pushes,
          remaining, 0n,
          candidates, squares,
          Exact.Value{4,
            Rules.State{wk, bk,
              pc, 0}})),
        zero_eq_one_absurd(phase_eq))
    case pushes remaining
         2n+more candidates
         Resource.PawnWhiteValue{
           wk, bk, pc}:
      Empty.absurd(
        Laws.Truth(Exact.win(pushes,
          remaining, 2n+more,
          candidates, squares,
          Exact.Value{4,
            Rules.State{wk, bk,
              pc, 0}})),
        two_plus_nat_eq_one_absurd(
          more, phase_eq))
    case pushes remaining 0n
         candidates
         Resource.PawnBlackValue{
           wk, bk, pc}:
      Empty.absurd(
        Laws.Truth(Exact.win(pushes,
          remaining, 0n,
          candidates, squares,
          Exact.Value{4,
            Rules.State{wk, bk,
              pc, 1}})),
        zero_eq_one_absurd(phase_eq))
    case pushes remaining
         2n+more candidates
         Resource.PawnBlackValue{
           wk, bk, pc}:
      Empty.absurd(
        Laws.Truth(Exact.win(pushes,
          remaining, 2n+more,
          candidates, squares,
          Exact.Value{4,
            Rules.State{wk, bk,
              pc, 1}})),
        two_plus_nat_eq_one_absurd(
          more, phase_eq))
    case pushes remaining
         1n+more candidates
         Resource.PawnKing{wk,
           bk, pc}:
      Empty.absurd(
        Laws.Truth(Exact.win(pushes,
          remaining, 1n+more,
          candidates, squares,
          Exact.King{4,
            wk, bk, pc})),
        positive_nat_eq_zero_absurd(
          more, phase_eq))
    case pushes remaining
         1n+more candidates
         Resource.PawnPiece{wk,
           bk, pc}:
      Empty.absurd(
        Laws.Truth(Exact.win(pushes,
          remaining, 1n+more,
          candidates, squares,
          Exact.Piece{4,
            wk, bk, pc})),
        positive_nat_eq_zero_absurd(
          more, phase_eq))
    case pushes remaining
         1n+more candidates
         Resource.PawnBlackAll{
           wk, bk, pc,
           all_so_far}:
      Empty.absurd(
        Laws.Truth(Exact.win(pushes,
          remaining, 1n+more,
          candidates, squares,
          Exact.BlackAll{4,
            wk, bk, pc,
            all_so_far})),
        positive_nat_eq_zero_absurd(
          more, phase_eq))

def Laws.generated_nonpawn_strategy_sound(
  remaining, clock, kind,
  squares, paths, cover,
  zero, no_pawn, budget,
  wk, bk, pc, turn,
  valid, same, yes):
  match turn:
    case True{}:
      +state = {Rules.State{wk,
        bk, pc, 1} : Rules.State}
      +stored = U32.is_ne(
        ProofTree.get_index(
          ClockedTables.nonpawn.go(
            remaining, clock,
            kind, squares,
            paths, zero),
          Rules.index(state)), 0)
      +scalar = Minimax.value(
        remaining, clock, squares,
        kind, state)
      Laws.nonpawn_black_value_strategy_sound(
        remaining, clock,
        squares, kind, wk,
        bk, pc, same,
        no_pawn,
        equality_cast(Bool,
          Laws.Truth,
          stored, scalar,
          Laws.generated_nonpawn_value_is_minimax(
            remaining, clock,
            kind, squares,
            paths, cover, zero,
            no_pawn, budget,
            state, valid), yes))
    case False{}:
      +state = {Rules.State{wk,
        bk, pc, 0} : Rules.State}
      +stored = U32.is_ne(
        ProofTree.get_index(
          ClockedTables.nonpawn.go(
            remaining, clock,
            kind, squares,
            paths, zero),
          Rules.index(state)), 0)
      +scalar = Minimax.value(
        remaining, clock, squares,
        kind, state)
      Laws.nonpawn_white_value_strategy_sound(
        remaining, clock,
        squares, kind, wk,
        bk, pc, same,
        no_pawn,
        equality_cast(Bool,
          Laws.Truth,
          stored, scalar,
          Laws.generated_nonpawn_value_is_minimax(
            remaining, clock,
            kind, squares,
            paths, cover, zero,
            no_pawn, budget,
            state, valid), yes))

def Laws.generated_nonpawn_strategy_complete(
  remaining, clock, kind,
  squares, paths, cover,
  zero, no_pawn, major,
  budget, wk, bk, pc,
  turn, valid, same,
  strategy):
  match turn:
    case True{}:
      +state = {Rules.State{wk,
        bk, pc, 1} : Rules.State}
      +stored = U32.is_ne(
        ProofTree.get_index(
          ClockedTables.nonpawn.go(
            remaining, clock,
            kind, squares,
            paths, zero),
          Rules.index(state)), 0)
      +scalar = Minimax.value(
        remaining, clock, squares,
        kind, state)
      equality_cast(Bool,
        Laws.Truth,
        scalar, stored,
        Equal.sym(Bool,
          stored, scalar,
          Laws.generated_nonpawn_value_is_minimax(
            remaining, clock,
            kind, squares,
            paths, cover, zero,
            no_pawn, budget,
            state, valid)),
        Laws.nonpawn_black_value_strategy_complete(
          remaining, clock,
          squares, kind, wk,
          bk, pc, same,
          major, no_pawn,
          strategy))
    case False{}:
      +state = {Rules.State{wk,
        bk, pc, 0} : Rules.State}
      +stored = U32.is_ne(
        ProofTree.get_index(
          ClockedTables.nonpawn.go(
            remaining, clock,
            kind, squares,
            paths, zero),
          Rules.index(state)), 0)
      +scalar = Minimax.value(
        remaining, clock, squares,
        kind, state)
      equality_cast(Bool,
        Laws.Truth,
        scalar, stored,
        Equal.sym(Bool,
          stored, scalar,
          Laws.generated_nonpawn_value_is_minimax(
            remaining, clock,
            kind, squares,
            paths, cover, zero,
            no_pawn, budget,
            state, valid)),
        Laws.nonpawn_white_value_strategy_complete(
          remaining, clock,
          squares, kind, wk,
          bk, pc, same,
          major, no_pawn,
          strategy))

def Laws.generated_pawn_strategy_sound(
  pushes, squares, paths,
  cover, queen, rook, zero,
  queen_cert, rook_cert,
  wk, bk, pc, turn,
  valid, same, yes):
  match turn:
    case True{}:
      +state = {Rules.State{wk,
        bk, pc, 1} : Rules.State}
      +stored = U32.is_ne(
        ProofTree.get_index(
          ClockedTables.pawn.budget.go(
            pushes, squares, paths,
            queen, rook, zero),
          Rules.index(state)), 0)
      +scalar = Exact.value(pushes,
        100n, squares, 4, state)
      Laws.pawn_strategy_sound(
        pushes, 100n, 1n,
        squares, squares,
        Resource.PawnBlackValue{
          wk, bk, pc},
        {==}, same,
        equality_cast(Bool,
          Laws.Truth,
          stored, scalar,
          Laws.generated_pawn_value_is_exact(
            pushes, squares,
            paths, cover,
            queen, rook, zero,
            queen_cert, rook_cert,
            state, valid),
          yes))
    case False{}:
      +state = {Rules.State{wk,
        bk, pc, 0} : Rules.State}
      +stored = U32.is_ne(
        ProofTree.get_index(
          ClockedTables.pawn.budget.go(
            pushes, squares, paths,
            queen, rook, zero),
          Rules.index(state)), 0)
      +scalar = Exact.value(pushes,
        100n, squares, 4, state)
      Laws.pawn_strategy_sound(
        pushes, 100n, 1n,
        squares, squares,
        Resource.PawnWhiteValue{
          wk, bk, pc},
        {==}, same,
        equality_cast(Bool,
          Laws.Truth,
          stored, scalar,
          Laws.generated_pawn_value_is_exact(
            pushes, squares,
            paths, cover,
            queen, rook, zero,
            queen_cert, rook_cert,
            state, valid),
          yes))

def Laws.generated_pawn_strategy_complete(
  pushes, squares, paths,
  cover, queen, rook, zero,
  queen_cert, rook_cert,
  wk, bk, pc, turn,
  valid, same, strategy):
  match turn:
    case True{}:
      +state = {Rules.State{wk,
        bk, pc, 1} : Rules.State}
      +stored = U32.is_ne(
        ProofTree.get_index(
          ClockedTables.pawn.budget.go(
            pushes, squares, paths,
            queen, rook, zero),
          Rules.index(state)), 0)
      +scalar = Exact.value(pushes,
        100n, squares, 4, state)
      equality_cast(Bool,
        Laws.Truth,
        scalar, stored,
        Equal.sym(Bool,
          stored, scalar,
          Laws.generated_pawn_value_is_exact(
            pushes, squares,
            paths, cover,
            queen, rook, zero,
            queen_cert, rook_cert,
            state, valid)),
        Laws.pawn_strategy_complete(
          pushes, 100n, 1n,
          squares, squares,
          Resource.PawnBlackValue{
            wk, bk, pc},
          {==}, same,
          strategy))
    case False{}:
      +state = {Rules.State{wk,
        bk, pc, 0} : Rules.State}
      +stored = U32.is_ne(
        ProofTree.get_index(
          ClockedTables.pawn.budget.go(
            pushes, squares, paths,
            queen, rook, zero),
          Rules.index(state)), 0)
      +scalar = Exact.value(pushes,
        100n, squares, 4, state)
      equality_cast(Bool,
        Laws.Truth,
        scalar, stored,
        Equal.sym(Bool,
          stored, scalar,
          Laws.generated_pawn_value_is_exact(
            pushes, squares,
            paths, cover,
            queen, rook, zero,
            queen_cert, rook_cert,
            state, valid)),
        Laws.pawn_strategy_complete(
          pushes, 100n, 1n,
          squares, squares,
          Resource.PawnWhiteValue{
            wk, bk, pc},
          {==}, same,
          strategy))

def Laws.nonpawn_serialized_byte_one_sound(
  remaining, clock, kind,
  squares, paths, cover,
  full, zero, no_pawn,
  budget, wk, bk, pc,
  turn, valid, same,
  read_one):
  match turn:
    case True{}:
      +state = {Rules.State{wk,
        bk, pc, 1} : Rules.State}
      +bytes = ProofTree.bytes(
        ClockedTables.nonpawn.go(
          remaining, clock, kind,
          squares, paths, zero))
      +offset = ProofTree.byte_offset(
        19n, ProofTree.bits19(
          Rules.index(state)))
      +scalar = Minimax.value(
        remaining, clock,
        squares, kind, state)
      Laws.nonpawn_black_value_strategy_sound(
        remaining, clock,
        squares, kind, wk,
        bk, pc, same,
        no_pawn,
        serialized_byte_one_sound(
          bytes, offset, scalar,
          Laws.generated_nonpawn_serialized_valid_state(
            remaining, clock,
            kind, squares,
            paths, cover, full,
            zero, no_pawn,
            budget, state,
            valid), read_one))
    case False{}:
      +state = {Rules.State{wk,
        bk, pc, 0} : Rules.State}
      +bytes = ProofTree.bytes(
        ClockedTables.nonpawn.go(
          remaining, clock, kind,
          squares, paths, zero))
      +offset = ProofTree.byte_offset(
        19n, ProofTree.bits19(
          Rules.index(state)))
      +scalar = Minimax.value(
        remaining, clock,
        squares, kind, state)
      Laws.nonpawn_white_value_strategy_sound(
        remaining, clock,
        squares, kind, wk,
        bk, pc, same,
        no_pawn,
        serialized_byte_one_sound(
          bytes, offset, scalar,
          Laws.generated_nonpawn_serialized_valid_state(
            remaining, clock,
            kind, squares,
            paths, cover, full,
            zero, no_pawn,
            budget, state,
            valid), read_one))

def Laws.nonpawn_serialized_byte_one_complete(
  remaining, clock, kind,
  squares, paths, cover,
  full, zero, no_pawn,
  major, budget,
  wk, bk, pc, turn,
  valid, same, strategy):
  match turn:
    case True{}:
      +state = {Rules.State{wk,
        bk, pc, 1} : Rules.State}
      +bytes = ProofTree.bytes(
        ClockedTables.nonpawn.go(
          remaining, clock, kind,
          squares, paths, zero))
      +offset = ProofTree.byte_offset(
        19n, ProofTree.bits19(
          Rules.index(state)))
      +scalar = Minimax.value(
        remaining, clock,
        squares, kind, state)
      serialized_byte_one_complete(
        bytes, offset, scalar,
        Laws.generated_nonpawn_serialized_valid_state(
          remaining, clock,
          kind, squares,
          paths, cover, full,
          zero, no_pawn,
          budget, state,
          valid),
        Laws.nonpawn_black_value_strategy_complete(
          remaining, clock,
          squares, kind, wk,
          bk, pc, same,
          major, no_pawn,
          strategy))
    case False{}:
      +state = {Rules.State{wk,
        bk, pc, 0} : Rules.State}
      +bytes = ProofTree.bytes(
        ClockedTables.nonpawn.go(
          remaining, clock, kind,
          squares, paths, zero))
      +offset = ProofTree.byte_offset(
        19n, ProofTree.bits19(
          Rules.index(state)))
      +scalar = Minimax.value(
        remaining, clock,
        squares, kind, state)
      serialized_byte_one_complete(
        bytes, offset, scalar,
        Laws.generated_nonpawn_serialized_valid_state(
          remaining, clock,
          kind, squares,
          paths, cover, full,
          zero, no_pawn,
          budget, state,
          valid),
        Laws.nonpawn_white_value_strategy_complete(
          remaining, clock,
          squares, kind, wk,
          bk, pc, same,
          major, no_pawn,
          strategy))

def Laws.pawn_serialized_byte_one_sound(
  pushes, squares, paths,
  cover, full, queen, rook,
  zero, queen_cert,
  rook_cert, wk, bk, pc,
  turn, valid, same,
  read_one):
  match turn:
    case True{}:
      +state = {Rules.State{wk,
        bk, pc, 1} : Rules.State}
      +bytes = ProofTree.bytes(
        ClockedTables.pawn.budget.go(
          pushes, squares,
          paths, queen,
          rook, zero))
      +offset = ProofTree.byte_offset(
        19n, ProofTree.bits19(
          Rules.index(state)))
      +scalar = Exact.value(pushes,
        100n, squares, 4,
        state)
      Laws.pawn_strategy_sound(
        pushes, 100n, 1n,
        squares, squares,
        Resource.PawnBlackValue{
          wk, bk, pc},
        {==}, same,
        serialized_byte_one_sound(
          bytes, offset, scalar,
          Laws.generated_pawn_serialized_valid_state(
            pushes, squares,
            paths, cover, full,
            queen, rook, zero,
            queen_cert, rook_cert,
            state, valid),
          read_one))
    case False{}:
      +state = {Rules.State{wk,
        bk, pc, 0} : Rules.State}
      +bytes = ProofTree.bytes(
        ClockedTables.pawn.budget.go(
          pushes, squares,
          paths, queen,
          rook, zero))
      +offset = ProofTree.byte_offset(
        19n, ProofTree.bits19(
          Rules.index(state)))
      +scalar = Exact.value(pushes,
        100n, squares, 4,
        state)
      Laws.pawn_strategy_sound(
        pushes, 100n, 1n,
        squares, squares,
        Resource.PawnWhiteValue{
          wk, bk, pc},
        {==}, same,
        serialized_byte_one_sound(
          bytes, offset, scalar,
          Laws.generated_pawn_serialized_valid_state(
            pushes, squares,
            paths, cover, full,
            queen, rook, zero,
            queen_cert, rook_cert,
            state, valid),
          read_one))

def Laws.pawn_serialized_byte_one_complete(
  pushes, squares, paths,
  cover, full, queen, rook,
  zero, queen_cert,
  rook_cert, wk, bk, pc,
  turn, valid, same,
  strategy):
  match turn:
    case True{}:
      +state = {Rules.State{wk,
        bk, pc, 1} : Rules.State}
      +bytes = ProofTree.bytes(
        ClockedTables.pawn.budget.go(
          pushes, squares,
          paths, queen,
          rook, zero))
      +offset = ProofTree.byte_offset(
        19n, ProofTree.bits19(
          Rules.index(state)))
      +scalar = Exact.value(pushes,
        100n, squares, 4,
        state)
      serialized_byte_one_complete(
        bytes, offset, scalar,
        Laws.generated_pawn_serialized_valid_state(
          pushes, squares,
          paths, cover, full,
          queen, rook, zero,
          queen_cert, rook_cert,
          state, valid),
        Laws.pawn_strategy_complete(
          pushes, 100n, 1n,
          squares, squares,
          Resource.PawnBlackValue{
            wk, bk, pc},
          {==}, same,
          strategy))
    case False{}:
      +state = {Rules.State{wk,
        bk, pc, 0} : Rules.State}
      +bytes = ProofTree.bytes(
        ClockedTables.pawn.budget.go(
          pushes, squares,
          paths, queen,
          rook, zero))
      +offset = ProofTree.byte_offset(
        19n, ProofTree.bits19(
          Rules.index(state)))
      +scalar = Exact.value(pushes,
        100n, squares, 4,
        state)
      serialized_byte_one_complete(
        bytes, offset, scalar,
        Laws.generated_pawn_serialized_valid_state(
          pushes, squares,
          paths, cover, full,
          queen, rook, zero,
          queen_cert, rook_cert,
          state, valid),
        Laws.pawn_strategy_complete(
          pushes, 100n, 1n,
          squares, squares,
          Resource.PawnWhiteValue{
            wk, bk, pc},
          {==}, same,
          strategy))

def Laws.nonpawn_serialized_byte_zero_refutes_win(
  remaining, clock, kind,
  squares, paths, cover,
  full, zero, no_pawn,
  major, budget,
  wk, bk, pc, turn,
  valid, same,
  read_zero, strategy):
  +read = List.get(&2, U32,
    ProofTree.bytes(
      ClockedTables.nonpawn.go(
        remaining, clock,
        kind, squares,
        paths, zero)),
    ProofTree.byte_offset(19n,
      ProofTree.bits19(
        Rules.index(Rules.State{
          wk, bk, pc,
          Bool.pick(U32,
            turn, 1, 0)}))))
  zero_byte_cannot_equal_one(
    Equal.trans(Maybe<&2, U32>,
      Some{0}, read, Some{1},
      Equal.sym(Maybe<&2,
        U32>, read, Some{0},
        read_zero),
      Laws.nonpawn_serialized_byte_one_complete(
        remaining, clock,
        kind, squares,
        paths, cover, full,
        zero, no_pawn,
        major, budget,
        wk, bk, pc,
        turn, valid,
        same, strategy)))

def Laws.pawn_serialized_byte_zero_refutes_win(
  pushes, squares, paths,
  cover, full, queen, rook,
  zero, queen_cert,
  rook_cert, wk, bk, pc,
  turn, valid, same,
  read_zero, strategy):
  +read = List.get(&2, U32,
    ProofTree.bytes(
      ClockedTables.pawn.budget.go(
        pushes, squares,
        paths, queen,
        rook, zero)),
    ProofTree.byte_offset(19n,
      ProofTree.bits19(
        Rules.index(Rules.State{
          wk, bk, pc,
          Bool.pick(U32,
            turn, 1, 0)}))))
  zero_byte_cannot_equal_one(
    Equal.trans(Maybe<&2, U32>,
      Some{0}, read, Some{1},
      Equal.sym(Maybe<&2,
        U32>, read, Some{0},
        read_zero),
      Laws.pawn_serialized_byte_one_complete(
        pushes, squares,
        paths, cover, full,
        queen, rook, zero,
        queen_cert, rook_cert,
        wk, bk, pc,
        turn, valid, same,
        strategy)))

def black_clock_value_split(
  +kind: U32, +wk: U32, +bk: U32,
  +pc: U32, +scan: Retro.BlackReplyScan,
  yes: Laws.Truth(ClockedStep.black_value.fin(
    kind, wk, bk, pc, scan))) ->
  Laws.Truth(Bool.not(Laws.BlackScanSeen(scan)) &&
    Rules.attacks(kind, pc, bk, wk)) |
  (Laws.Truth(Laws.BlackScanSeen(scan)) &
   Laws.Truth(Laws.BlackScanAll(scan))):
  match scan:
    case Retro.BlackReplyScan{seen, all_won, maximum}:
      or_cases(
        Laws.Truth(Bool.not(seen) &&
          Rules.attacks(kind, pc, bk, wk)) |
        (Laws.Truth(seen) & Laws.Truth(all_won)),
        Bool.not(seen) &&
          Rules.attacks(kind, pc, bk, wk),
        seen && all_won, yes,
        left => Inl{left},
        +right => Inr{(
          and_left(seen, all_won, right),
          and_right(seen, all_won, right))})

def black_clock_step_sound_no_moves(
  +squares: List<&2, U32>,
  +kind: U32, +wk: U32, +bk: U32,
  +pc: U32, +next: ProofTree.Tree,
  +valid: Laws.Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, 1})),
  complete: @dest: U32 ->
    Laws.Truth(U32.is_lt(dest, 64)) ->
    Squares.Member(U32, dest, squares),
  +scan: Retro.BlackReplyScan,
  seen_eq: {Laws.BlackScanSeen(scan) ==
    Retro.black_has_move.squares(kind, wk,
      bk, pc, squares, False{}) : Bool},
  +first: Laws.Truth(
    Bool.not(Laws.BlackScanSeen(scan)) &&
      Rules.attacks(kind, pc, bk, wk))) ->
  WDL.BlackMate(kind, wk, bk, pc):
  no_seen = and_left(Bool.not(
    Laws.BlackScanSeen(scan)),
    Rules.attacks(kind, pc, bk, wk), first)
  attacks = and_right(Bool.not(
    Laws.BlackScanSeen(scan)),
    Rules.attacks(kind, pc, bk, wk), first)
  no_move = equality_cast(Bool,
    value => Laws.Truth(Bool.not(value)),
    Laws.BlackScanSeen(scan),
    Retro.black_has_move.squares(kind, wk,
      bk, pc, squares, False{}),
    seen_eq, no_seen)
  terminal = and_intro(Bool.not(
    Retro.black_has_move.squares(kind, wk,
      bk, pc, squares, False{})),
    Rules.attacks(kind, pc, bk, wk),
    no_move, attacks)
  Laws.clocked_step_black_terminal_sound(
    squares, kind, wk, bk, pc,
    valid, complete, terminal)

def black_clock_step_sound_replies(
  +squares: List<&2, U32>,
  +kind: U32, +clock: Nat,
  +wk: U32, +bk: U32, +pc: U32,
  +next: ProofTree.Tree,
  +scan: Retro.BlackReplyScan,
  scan_eq: {scan ==
    Retro.black_reply_scan.squares(kind, wk,
      bk, pc, squares, next,
      Retro.BlackReplyScan{False{}, True{}, 0}) :
    Retro.BlackReplyScan},
  seen_eq: {Laws.BlackScanSeen(scan) ==
    Retro.black_has_move.squares(kind, wk,
      bk, pc, squares, False{}) : Bool},
  before: Laws.Truth(Nat.is_lt(clock, 100n)),
  pair: Laws.Truth(Laws.BlackScanSeen(scan)) &
    Laws.Truth(Laws.BlackScanAll(scan))) ->
  Laws.BlackClockStep(squares, kind, clock,
    wk, bk, pc, next):
  match pair:
    case (seen, all):
      has_move = equality_cast(Bool,
        value => Laws.Truth(value),
        Laws.BlackScanSeen(scan),
        Retro.black_has_move.squares(kind,
          wk, bk, pc, squares, False{}),
        seen_eq, seen)
      legal = Laws.black_has_move_squares_sound(
        squares, kind, wk, bk, pc,
        has_move)
      all_actual = equality_cast(
        Retro.BlackReplyScan,
        value => Laws.Truth(
          Laws.BlackScanAll(value)),
        scan,
        Retro.black_reply_scan.squares(kind,
          wk, bk, pc, squares, next,
          Retro.BlackReplyScan{False{}, True{}, 0}),
        scan_eq, all)
      safe = Laws.black_reply_square_scan_all_sound(
        squares, kind, wk, bk, pc, next,
        Retro.BlackReplyScan{False{}, True{}, 0},
        all_actual)
      Inr{(laws_truth_to_wdl_truth(
        Nat.is_lt(clock, 100n), before),
        (legal, safe))}

def black_clock_step_sound_split(
  +squares: List<&2, U32>,
  +kind: U32, +clock: Nat,
  +wk: U32, +bk: U32, +pc: U32,
  +next: ProofTree.Tree,
  +valid: Laws.Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, 1})),
  complete: @dest: U32 ->
    Laws.Truth(U32.is_lt(dest, 64)) ->
    Squares.Member(U32, dest, squares),
  +scan: Retro.BlackReplyScan,
  scan_eq: {scan ==
    Retro.black_reply_scan.squares(kind, wk,
      bk, pc, squares, next,
      Retro.BlackReplyScan{False{}, True{}, 0}) :
    Retro.BlackReplyScan},
  seen_eq: {Laws.BlackScanSeen(scan) ==
    Retro.black_has_move.squares(kind, wk,
      bk, pc, squares, False{}) : Bool},
  before: Laws.Truth(Nat.is_lt(clock, 100n)),
  split:
    Laws.Truth(Bool.not(
      Laws.BlackScanSeen(scan)) &&
      Rules.attacks(kind, pc, bk, wk)) |
    (Laws.Truth(Laws.BlackScanSeen(scan)) &
     Laws.Truth(Laws.BlackScanAll(scan)))) ->
  Laws.BlackClockStep(squares, kind, clock,
    wk, bk, pc, next):
  match split:
    case Inl{no_moves}:
      Inl{black_clock_step_sound_no_moves(
        squares, kind, wk, bk, pc, next,
        valid, complete, scan, seen_eq,
        no_moves)}
    case Inr{replies}:
      black_clock_step_sound_replies(
        squares, kind, clock, wk, bk, pc,
        next, scan, scan_eq, seen_eq, before,
        replies)

def black_clock_step_sound_value(
  +squares: List<&2, U32>,
  +kind: U32, +clock: Nat,
  +wk: U32, +bk: U32, +pc: U32,
  +next: ProofTree.Tree,
  +valid: Laws.Truth(Rules.valid(kind,
    Rules.State{wk, bk, pc, 1})),
  complete: @dest: U32 ->
    Laws.Truth(U32.is_lt(dest, 64)) ->
    Squares.Member(U32, dest, squares),
  +scan: Retro.BlackReplyScan,
  scan_eq: {scan ==
    Retro.black_reply_scan.squares(kind, wk,
      bk, pc, squares, next,
      Retro.BlackReplyScan{False{}, True{}, 0}) :
    Retro.BlackReplyScan},
  seen_eq: {Laws.BlackScanSeen(scan) ==
    Retro.black_has_move.squares(kind, wk,
      bk, pc, squares, False{}) : Bool},
  before: Laws.Truth(Nat.is_lt(clock, 100n)),
  yes: Laws.Truth(ClockedStep.black_value.fin(
    kind, wk, bk, pc, scan))) ->
  Laws.BlackClockStep(squares, kind, clock,
    wk, bk, pc, next):
  black_clock_step_sound_split(squares, kind,
    clock, wk, bk, pc, next, valid,
    complete, scan, scan_eq, seen_eq, before,
    black_clock_value_split(kind, wk, bk,
      pc, scan, yes))

def Laws.clocked_black_step_sound(
  squares, kind, clock, wk, bk, pc,
  next, valid, complete_mate,
  complete_scan, yes):
  +scan = Retro.black_reply_scan.squares(kind,
    wk, bk, pc, squares, next,
    Retro.BlackReplyScan{False{}, True{}, 0})
  seen_eq = Laws.black_reply_scan_seen_matches_has_move(
    squares, kind, wk, bk, pc, next,
    Retro.BlackReplyScan{False{}, True{}, 0})
  +terminal = ClockedStep.black_terminal(kind,
    wk, bk, pc, squares)
  +before = Nat.is_lt(clock, 100n)
  +value = ClockedStep.black_value.fin(kind,
    wk, bk, pc, scan)
  or_cases(Laws.BlackClockStep(squares, kind,
      clock, wk, bk, pc, next),
    terminal, before && value, yes,
    mate => Inl{
      Laws.clocked_step_black_terminal_sound(
        squares, kind, wk, bk, pc, valid,
        complete_mate, mate)},
    +continuation =>
      black_clock_step_sound_value(squares,
        kind, clock, wk, bk, pc, next,
        valid, complete_scan, scan, {==},
        seen_eq,
        and_left(before, value, continuation),
        and_right(before, value,
          continuation)))

def black_clock_value_from_seen_all(
  +kind: U32, +wk: U32, +bk: U32,
  +pc: U32, +scan: Retro.BlackReplyScan,
  seen: Laws.Truth(Laws.BlackScanSeen(scan)),
  all: Laws.Truth(Laws.BlackScanAll(scan))) ->
  Laws.Truth(ClockedStep.black_value.fin(
    kind, wk, bk, pc, scan)):
  match scan:
    case Retro.BlackReplyScan{seen_flag,
         all_won, maximum}:
      or_right(Bool.not(seen_flag) &&
        Rules.attacks(kind, pc, bk, wk),
        seen_flag && all_won,
        and_intro(seen_flag, all_won,
          seen, all))

def Laws.clocked_black_step_complete(
  squares, kind, clock, wk, bk, pc,
  next, evidence):
  match evidence:
    case Inl{mate}:
      or_left(ClockedStep.black_terminal(kind,
          wk, bk, pc, squares),
        Nat.is_lt(clock, 100n) &&
          ClockedStep.black_value(kind, wk,
            bk, pc, squares, next),
        Laws.clocked_step_black_terminal_complete(
          squares, kind, wk, bk, pc,
          mate))
    case Inr{nonmate}:
      match nonmate:
        case Tuple{before_proof,
             Tuple{legal, safe}}:
          +scan = Retro.black_reply_scan.squares(kind,
            wk, bk, pc, squares, next,
            Retro.BlackReplyScan{False{}, True{}, 0})
          +terminal = ClockedStep.black_terminal(kind,
            wk, bk, pc, squares)
          +before = Nat.is_lt(clock, 100n)
          +value = ClockedStep.black_value.fin(kind,
            wk, bk, pc, scan)
          has_move = Laws.black_has_move_squares_complete(
            squares, kind, wk, bk, pc,
            False{}, legal)
          seen_eq = Laws.black_reply_scan_seen_matches_has_move(
            squares, kind, wk, bk, pc, next,
            Retro.BlackReplyScan{False{}, True{}, 0})
          seen = equality_cast(Bool,
            value => Laws.Truth(value),
            Retro.black_has_move.squares(kind,
              wk, bk, pc, squares, False{}),
            Laws.BlackScanSeen(scan),
            Equal.sym(Bool,
              Laws.BlackScanSeen(scan),
              Retro.black_has_move.squares(kind,
                wk, bk, pc, squares, False{}),
              seen_eq), has_move)
          all = Laws.black_reply_square_scan_all_complete(
            squares, kind, wk, bk, pc, next,
            Retro.BlackReplyScan{False{}, True{}, 0},
            Unit{}, safe)
          value_yes = black_clock_value_from_seen_all(
            kind, wk, bk, pc, scan, seen, all)
          or_right(terminal, before && value,
            and_intro(before, value,
              wdl_truth_to_laws_truth(before,
                before_proof), value_yes))

def white_promotion_step_sound(
  +wk: U32, +bk: U32, +pc: U32,
  +queen: ProofTree.Tree,
  +rook: ProofTree.Tree,
  yes: Laws.Truth(ClockedStep.white_promotion(
    wk, bk, pc, queen, rook))) ->
  Laws.WhitePromotionStep(wk, bk, pc,
    queen, rook):
  +target = (pc + 8 : U32)
  +index = Rules.index(Rules.State{
    wk, bk, target, 1})
  +qmove = WDL.promotion(wk, bk, pc,
    0, wk, bk, target)
  +qwin = U32.is_ne(ProofTree.get_index(
    queen, index), 0)
  +rmove = WDL.promotion(wk, bk, pc,
    1, wk, bk, target)
  +rwin = U32.is_ne(ProofTree.get_index(
    rook, index), 0)
  or_cases(Laws.WhitePromotionStep(wk, bk,
      pc, queen, rook),
    qmove && qwin, rmove && rwin, yes,
    queen_yes => Inl{truth_and_split(
      qmove, qwin, queen_yes)},
    rook_yes => Inr{truth_and_split(
      rmove, rwin, rook_yes)})

def white_promotion_step_complete(
  +wk: U32, +bk: U32, +pc: U32,
  +queen: ProofTree.Tree,
  +rook: ProofTree.Tree,
  evidence: Laws.WhitePromotionStep(wk,
    bk, pc, queen, rook)) ->
  Laws.Truth(ClockedStep.white_promotion(
    wk, bk, pc, queen, rook)):
  match evidence:
    case Inl{queen_yes}:
      match queen_yes:
        case (legal, win):
          +target = (pc + 8 : U32)
          +index = Rules.index(Rules.State{
            wk, bk, target, 1})
          +qmove = WDL.promotion(wk, bk, pc,
            0, wk, bk, target)
          +qwin = U32.is_ne(ProofTree.get_index(
            queen, index), 0)
          +rmove = WDL.promotion(wk, bk, pc,
            1, wk, bk, target)
          +rwin = U32.is_ne(ProofTree.get_index(
            rook, index), 0)
          or_left(qmove && qwin,
            rmove && rwin,
            and_intro(qmove, qwin, legal, win))
    case Inr{rook_yes}:
      match rook_yes:
        case (legal, win):
          +target = (pc + 8 : U32)
          +index = Rules.index(Rules.State{
            wk, bk, target, 1})
          +qmove = WDL.promotion(wk, bk, pc,
            0, wk, bk, target)
          +qwin = U32.is_ne(ProofTree.get_index(
            queen, index), 0)
          +rmove = WDL.promotion(wk, bk, pc,
            1, wk, bk, target)
          +rwin = U32.is_ne(ProofTree.get_index(
            rook, index), 0)
          or_right(qmove && qwin,
            rmove && rwin,
            and_intro(rmove, rwin, legal, win))

def white_promotion_branch_sound(
  +kind: U32, +wk: U32, +bk: U32,
  +pc: U32, +queen: ProofTree.Tree,
  +rook: ProofTree.Tree,
  +yes: Laws.Truth(U32.is_eq(kind, 4) &&
    ClockedStep.white_promotion(wk, bk, pc,
      queen, rook))) ->
  Laws.Truth(U32.is_eq(kind, 4)) &
  Laws.WhitePromotionStep(wk, bk, pc,
    queen, rook):
  +promotion = ClockedStep.white_promotion(
    wk, bk, pc, queen, rook)
  (and_left(U32.is_eq(kind, 4),
      promotion, yes),
    white_promotion_step_sound(wk, bk, pc,
      queen, rook,
      and_right(U32.is_eq(kind, 4),
        promotion, yes)))

def white_clock_value_sound(
  +squares: List<&2, U32>, +kind: U32,
  +wk: U32, +bk: U32, +pc: U32,
  +next: ProofTree.Tree,
  +reset: ProofTree.Tree,
  +queen: ProofTree.Tree,
  +rook: ProofTree.Tree,
  yes: Laws.Truth(ClockedStep.white_value(
    kind, wk, bk, pc, squares, next,
    reset, queen, rook))) ->
  Laws.WhiteClockChoices(squares, kind, wk,
    bk, pc, next, reset, queen, rook):
  +king = ClockedStep.white_king.go(squares,
    kind, Rules.State{wk, bk, pc, 0},
    wk, bk, pc, next)
  +piece = ClockedStep.white_piece.go(squares,
    kind, Rules.State{wk, bk, pc, 0},
    wk, bk, pc, next, reset)
  +promotion = U32.is_eq(kind, 4) &&
    ClockedStep.white_promotion(wk, bk, pc,
      queen, rook)
  or_cases(Laws.WhiteClockChoices(squares,
      kind, wk, bk, pc, next, reset,
      queen, rook), king || piece,
    promotion, yes,
    move_yes =>
      or_cases(Laws.WhiteClockChoices(squares,
          kind, wk, bk, pc, next, reset,
          queen, rook), king, piece,
        move_yes,
        king_yes => Inl{Inl{
          Laws.clocked_step_white_king_scan_sound(
            squares, kind, wk, bk, pc,
            next, king_yes)}},
        piece_yes => Inl{Inr{
          Laws.clocked_step_white_piece_scan_sound(
            squares, kind, wk, bk, pc,
            next, reset, piece_yes)}}),
    promotion_yes => Inr{
      white_promotion_branch_sound(kind, wk,
        bk, pc, queen, rook, promotion_yes)})

def white_clock_value_complete(
  +squares: List<&2, U32>, +kind: U32,
  +wk: U32, +bk: U32, +pc: U32,
  +next: ProofTree.Tree,
  +reset: ProofTree.Tree,
  +queen: ProofTree.Tree,
  +rook: ProofTree.Tree,
  evidence: Laws.WhiteClockChoices(squares,
    kind, wk, bk, pc, next, reset,
    queen, rook)) ->
  Laws.Truth(ClockedStep.white_value(kind,
    wk, bk, pc, squares, next, reset,
    queen, rook)):
  match evidence:
    case Inl{move}:
      match move:
        case Inl{king_witness}:
          +king = ClockedStep.white_king.go(squares,
            kind, Rules.State{wk, bk, pc, 0},
            wk, bk, pc, next)
          +piece = ClockedStep.white_piece.go(squares,
            kind, Rules.State{wk, bk, pc, 0},
            wk, bk, pc, next, reset)
          +promotion = U32.is_eq(kind, 4) &&
            ClockedStep.white_promotion(wk, bk,
              pc, queen, rook)
          or_left(king || piece, promotion,
            or_left(king, piece,
              Laws.clocked_step_white_king_scan_complete(
                squares, kind, wk, bk, pc,
                next, king_witness)))
        case Inr{piece_witness}:
          +king = ClockedStep.white_king.go(squares,
            kind, Rules.State{wk, bk, pc, 0},
            wk, bk, pc, next)
          +piece = ClockedStep.white_piece.go(squares,
            kind, Rules.State{wk, bk, pc, 0},
            wk, bk, pc, next, reset)
          +promotion = U32.is_eq(kind, 4) &&
            ClockedStep.white_promotion(wk, bk,
              pc, queen, rook)
          or_left(king || piece, promotion,
            or_right(king, piece,
              Laws.clocked_step_white_piece_scan_complete(
                squares, kind, wk, bk, pc,
                next, reset, piece_witness)))
    case Inr{promotion_witness}:
      match promotion_witness:
        case (pawn, promoted):
          +king = ClockedStep.white_king.go(squares,
            kind, Rules.State{wk, bk, pc, 0},
            wk, bk, pc, next)
          +piece = ClockedStep.white_piece.go(squares,
            kind, Rules.State{wk, bk, pc, 0},
            wk, bk, pc, next, reset)
          +promotion = ClockedStep.white_promotion(
            wk, bk, pc, queen, rook)
          or_right(king || piece,
            U32.is_eq(kind, 4) && promotion,
            and_intro(U32.is_eq(kind, 4),
              promotion, pawn,
              white_promotion_step_complete(
                wk, bk, pc, queen, rook,
                promoted)))

def Laws.clocked_white_step_sound(
  squares, kind, clock, wk, bk, pc,
  next, reset, queen, rook, yes):
  +before = Nat.is_lt(clock, 100n)
  +value = ClockedStep.white_value(kind,
    wk, bk, pc, squares, next, reset,
    queen, rook)
  (and_left(before, value, yes),
    white_clock_value_sound(squares, kind,
      wk, bk, pc, next, reset, queen,
      rook, and_right(before, value, yes)))

def Laws.clocked_white_step_complete(
  squares, kind, clock, wk, bk, pc,
  next, reset, queen, rook, evidence):
  match evidence:
    case (before_proof, choice):
      +before = Nat.is_lt(clock, 100n)
      +value = ClockedStep.white_value(kind,
        wk, bk, pc, squares, next, reset,
        queen, rook)
      and_intro(before, value,
        before_proof,
        white_clock_value_complete(squares,
          kind, wk, bk, pc, next, reset,
          queen, rook, choice))

def Laws.work_black_reply_scan_covers_legal_move(
  work, kind, wk, bk, pc, dest, complete, valid,
  move, all):
  range = Laws.legal_black_move_destination_in_range(
    kind, wk, bk, pc, dest, valid, move)
  member = complete(dest, range)
  safe = Laws.black_reply_square_scan_all_sound(
    Laws.WorkSquares(work), kind, wk, bk, pc,
    Laws.WorkWonTree(work),
    Retro.BlackReplyScan{False{}, True{}, 0}, all)
  Laws.black_scan_safe_member(Laws.WorkSquares(work),
    kind, wk, bk, pc, dest, Laws.WorkWonTree(work),
    member, safe, move)

def Laws.work_black_reply_scan_sees_legal_move(
  work, kind, wk, bk, pc, dest, complete, valid,
  move):
  range = Laws.legal_black_move_destination_in_range(
    kind, wk, bk, pc, dest, valid, move)
  member = complete(dest, range)
  legal = Laws.black_scan_legal_member(
    Laws.WorkSquares(work), kind, wk, bk, pc,
    dest, member, move)
  Laws.black_reply_square_scan_seen_complete(
    Laws.WorkSquares(work), kind, wk, bk, pc,
    Laws.WorkWonTree(work),
    Retro.BlackReplyScan{False{}, True{}, 0},
    legal)

def Laws.work_black_has_move_detects_legal_move(
  work, kind, wk, bk, pc, dest, complete, valid,
  move):
  range = Laws.legal_black_move_destination_in_range(
    kind, wk, bk, pc, dest, valid, move)
  member = complete(dest, range)
  legal = Laws.black_scan_legal_member(
    Laws.WorkSquares(work), kind, wk, bk, pc,
    dest, member, move)
  Laws.black_has_move_squares_complete(
    Laws.WorkSquares(work), kind, wk, bk, pc,
    False{}, legal)

def Laws.work_black_reply_scan_max_bounds_legal_move(
  work, kind, wk, bk, pc, dest, complete,
  valid, move):
  range = Laws.legal_black_move_destination_in_range(
    kind, wk, bk, pc, dest, valid, move)
  member = complete(dest, range)
  bound = Laws.black_reply_square_scan_max_bounds_legal(
    Laws.WorkSquares(work), kind, wk, bk, pc,
    Laws.WorkWonTree(work),
    Retro.BlackReplyScan{False{}, True{}, 0})
  Laws.black_scan_bound_member(
    Laws.WorkSquares(work), kind, wk, bk, pc,
    dest, Laws.WorkWonTree(work),
    Laws.BlackScanMaximum(Retro.black_reply_scan(
      kind, Rules.State{wk, bk, pc, 1},
      Laws.WorkWonTree(work),
      Laws.WorkSquares(work))),
    member, bound, move)

def Laws.work_black_reply_rank_decreases_if_no_overflow(
  work, kind, wk, bk, pc, dest, complete,
  valid, move, room):
  +maximum = Laws.BlackScanMaximum(
    Retro.black_reply_scan(kind,
      Rules.State{wk, bk, pc, 1},
      Laws.WorkWonTree(work), Laws.WorkSquares(work)))
  +successor = ProofTree.get_index(
    Laws.WorkWonTree(work),
    Rules.index(Rules.State{wk, dest, pc, 0}))
  Laws.u32_le_lt_transitive(successor, maximum,
    U32.inc(maximum),
    Laws.work_black_reply_scan_max_bounds_legal_move(
      work, kind, wk, bk, pc, dest,
      complete, valid, move),
    Laws.u32_inc_strict_below_max(maximum, room))

def Laws.zero_remaining_means_all_winning(xs, zero):
  match xs:
    case Nil{}:
      Unit{}
    case Con{h, t}:
      match h:
        case True{}:
          Laws.zero_remaining_means_all_winning(t, zero)
        case False{}:
          Empty.absurd(Laws.Truth(Logic.all_winning(False{} <> t)), zero)

def Laws.all_winning_means_zero_remaining(xs, all):
  match xs:
    case Nil{}:
      Unit{}
    case Con{h, t}:
      match h:
        case True{}:
          Laws.all_winning_means_zero_remaining(t, all)
        case False{}:
          Empty.absurd(Laws.Truth(Nat.is_eq(Logic.unresolved(False{} <> t), 0n)), all)

def Laws.resolving_one_decrements_remaining(before, after):
  match before:
    case Nil{}:
      {==}
    case Con{h, t}:
      match h:
        case True{}:
          Laws.resolving_one_decrements_remaining(t, after)
        case False{}:
          %Laws.resolving_one_decrements_remaining(t, after) :
            {1n+Logic.unresolved(Logic.join(t, False{} <> after)) ==
              1n+_ : Nat}
          {==}

def Laws.draw_exit_keeps_black_unresolved(before, after):
  match before:
    case Nil{}:
      Unit{}
    case Con{h, t}:
      match h:
        case True{}:
          Laws.draw_exit_keeps_black_unresolved(t, after)
        case False{}:
          Unit{}

def Laws.extension_reflexive(xs):
  match xs:
    case Nil{}:
      Unit{}
    case Con{h, t}:
      match h:
        case True{}:
          Laws.extension_reflexive(t)
        case False{}:
          Laws.extension_reflexive(t)

def Laws.resolving_one_only_adds_wins(before, after):
  match before:
    case Nil{}:
      Laws.extension_reflexive(after)
    case Con{h, t}:
      match h:
        case True{}:
          Laws.resolving_one_only_adds_wins(t, after)
        case False{}:
          Laws.resolving_one_only_adds_wins(t, after)

def Laws.white_attractor_monotone(old, new, extension, prior):
  match old new:
    case Nil{} Nil{}:
      Empty.absurd(Laws.Truth(Logic.any_winning(Nil{})), prior)
    case Nil{} Con{b, bs}:
      Empty.absurd(Laws.Truth(Logic.any_winning(b <> bs)), extension)
    case Con{a, as} Nil{}:
      Empty.absurd(Laws.Truth(Logic.any_winning(Nil{})), extension)
    case Con{True{}, as} Con{True{}, bs}:
      Unit{}
    case Con{True{}, as} Con{False{}, bs}:
      Empty.absurd(Laws.Truth(Logic.any_winning(False{} <> bs)), extension)
    case Con{False{}, as} Con{True{}, bs}:
      Unit{}
    case Con{False{}, as} Con{False{}, bs}:
      Laws.white_attractor_monotone(as, bs, extension, prior)

def Laws.black_attractor_monotone(old, new, extension, prior):
  match old new:
    case Nil{} Nil{}:
      Unit{}
    case Nil{} Con{b, bs}:
      Empty.absurd(Laws.Truth(Logic.all_winning(b <> bs)), extension)
    case Con{a, as} Nil{}:
      Empty.absurd(Laws.Truth(Logic.all_winning(Nil{})), extension)
    case Con{True{}, as} Con{True{}, bs}:
      Laws.black_attractor_monotone(as, bs, extension, prior)
    case Con{True{}, as} Con{False{}, bs}:
      Empty.absurd(Laws.Truth(Logic.all_winning(False{} <> bs)), extension)
    case Con{False{}, as} Con{True{}, bs}:
      Empty.absurd(Laws.Truth(Logic.all_winning(True{} <> bs)), prior)
    case Con{False{}, as} Con{False{}, bs}:
      Empty.absurd(Laws.Truth(Logic.all_winning(False{} <> bs)), prior)

def Laws.black_loss_monotone(check, old, new, extension, prior):
  match old new:
    case Nil{} Nil{}:
      prior
    case Nil{} Con{b, bs}:
      Empty.absurd(Laws.Truth(Logic.black_forced_loss(check, b <> bs)), extension)
    case Con{a, as} Nil{}:
      Empty.absurd(Laws.Truth(Logic.black_forced_loss(check, Nil{})), extension)
    case Con{a, as} Con{b, bs}:
      Laws.black_attractor_monotone(a <> as, b <> bs, extension, prior)

def Laws.bare_kings_never_win(n, win):
  match n:
    case 0n:
      win
    case 1n+rest:
      win

def Laws.winning_horizon_monotone(n, game, win):
  match n game:
    case 0n WDL.KingsOnly{}:
      win
    case 0n WDL.BareBishop{}:
      win
    case 0n WDL.BareKnight{}:
      win
    case 0n WDL.White{kind, wk, bk, pc}:
      Empty.absurd(WDL.WinWithin(1n, WDL.White{kind, wk, bk, pc}), win)
    case 0n WDL.Black{kind, wk, bk, pc}:
      Inl{win}
    case 1n+rest WDL.KingsOnly{}:
      win
    case 1n+rest WDL.BareBishop{}:
      win
    case 1n+rest WDL.BareKnight{}:
      win
    case 1n+rest WDL.White{kind, wk, bk, pc}:
      match win:
        case Tuple{+next, Tuple{legal, child}}:
          (next, (legal, Laws.winning_horizon_monotone(rest, next, child)))
    case 1n+rest WDL.Black{kind, wk, bk, pc}:
      match win:
        case Inl{mate}:
          Inl{mate}
        case Inr{pair}:
          match pair:
            case Tuple{has_move, replies}:
              Inr{(has_move, (+next => legal =>
                Laws.winning_horizon_monotone(rest, next,
                  replies(next, legal))))}

def Laws.bare_kings_are_not_white_win(win):
  match win:
    case Tuple{plies, within}:
      Laws.bare_kings_never_win(plies, within)

def Laws.capture_exit_refutes_white_win(n, kind, wk, bk, pc,
  capture, not_mate, win):
  match n:
    case 0n:
      not_mate(win)
    case 1n+rest:
      match win:
        case Inl{mate}:
          not_mate(mate)
        case Inr{pair}:
          match pair:
            case Tuple{has_move, replies}:
              Laws.bare_kings_never_win(rest,
                replies(WDL.KingsOnly{}, capture))

def Laws.legal_capture_is_not_checkmate(kind, wk, bk, pc, capture, mate):
  match mate:
    case Tuple{valid, Tuple{attacks, no_moves}}:
      no_moves((WDL.KingsOnly{}, capture))

def Laws.legal_capture_refutes_white_win(n, kind, wk, bk, pc,
  capture, win):
  Laws.capture_exit_refutes_white_win(n, kind, wk, bk, pc, capture,
    Laws.legal_capture_is_not_checkmate(kind, wk, bk, pc, capture), win)

def Laws.closed_set_contains_forced_wins(P, close, n, game, win):
  match n game:
    case 0n WDL.KingsOnly{}:
      Empty.absurd(P(WDL.KingsOnly{}), win)
    case 0n WDL.BareBishop{}:
      Empty.absurd(P(WDL.BareBishop{}), win)
    case 0n WDL.BareKnight{}:
      Empty.absurd(P(WDL.BareKnight{}), win)
    case 0n WDL.White{kind, wk, bk, pc}:
      Empty.absurd(P(WDL.White{kind, wk, bk, pc}), win)
    case 0n WDL.Black{kind, wk, bk, pc}:
      close(WDL.Black{kind, wk, bk, pc}, Inl{win})
    case 1n+rest WDL.KingsOnly{}:
      Empty.absurd(P(WDL.KingsOnly{}), win)
    case 1n+rest WDL.BareBishop{}:
      Empty.absurd(P(WDL.BareBishop{}), win)
    case 1n+rest WDL.BareKnight{}:
      Empty.absurd(P(WDL.BareKnight{}), win)
    case 1n+rest WDL.White{kind, wk, bk, pc}:
      match win:
        case Tuple{+next, Tuple{legal, child}}:
          close(WDL.White{kind, wk, bk, pc},
            (next, (legal,
              Laws.closed_set_contains_forced_wins(
                ~P, ~close, rest, next, child))))
    case 1n+rest WDL.Black{kind, wk, bk, pc}:
      match win:
        case Inl{mate}:
          close(WDL.Black{kind, wk, bk, pc}, Inl{mate})
        case Inr{pair}:
          match pair:
            case Tuple{has_move, replies}:
              close(WDL.Black{kind, wk, bk, pc},
                Inr{(has_move, (+next => legal =>
                  Laws.closed_set_contains_forced_wins(
                    ~P, ~close, rest, next, replies(next, legal))))})

def Laws.fifty_move_draw_on_white_turn(n, kind, wk, bk, pc, win):
  match n:
    case 0n:
      win
    case 1n+rest:
      match win:
        case Tuple{before_50, continuation}:
          before_50

def Laws.fifty_move_draw_on_black_turn_unless_mate(n, kind, wk, bk,
  pc, no_mate, win):
  match n:
    case 0n:
      no_mate(win)
    case 1n+rest:
      match win:
        case Inl{mate}:
          no_mate(mate)
        case Inr{pair}:
          match pair:
            case Tuple{before_50, Tuple{has_move, replies}}:
              before_50

def Laws.checkmate_is_terminal_win(clock, kind, wk, bk, pc, mate):
  mate

def Laws.stalemate_is_not_white_win(n, clock, kind, wk, bk, pc,
  no_move, no_mate, win):
  match n:
    case 0n:
      no_mate(win)
    case 1n+rest:
      match win:
        case Inl{mate}:
          no_mate(mate)
        case Inr{pair}:
          match pair:
            case Tuple{before_50, Tuple{has_move, replies}}:
              no_move(has_move)

def Laws.bare_bishop_is_not_white_win(n, clock, win):
  match n:
    case 0n:
      win
    case 1n+rest:
      win

def Laws.bare_knight_is_not_white_win(n, clock, win):
  match n:
    case 0n:
      win
    case 1n+rest:
      win

def Laws.closed_clocked_set_contains_forced_wins(P, close, n,
  clock, game, win):
  match n game:
    case 0n WDL.KingsOnly{}:
      Empty.absurd(P(Clocked.Timed{clock, WDL.KingsOnly{}}), win)
    case 0n WDL.BareBishop{}:
      Empty.absurd(P(Clocked.Timed{clock, WDL.BareBishop{}}), win)
    case 0n WDL.BareKnight{}:
      Empty.absurd(P(Clocked.Timed{clock, WDL.BareKnight{}}), win)
    case 0n WDL.White{kind, wk, bk, pc}:
      Empty.absurd(P(Clocked.Timed{clock,
        WDL.White{kind, wk, bk, pc}}), win)
    case 0n WDL.Black{kind, wk, bk, pc}:
      close(Clocked.Timed{clock, WDL.Black{kind, wk, bk, pc}},
        Inl{win})
    case 1n+rest WDL.KingsOnly{}:
      Empty.absurd(P(Clocked.Timed{clock, WDL.KingsOnly{}}), win)
    case 1n+rest WDL.BareBishop{}:
      Empty.absurd(P(Clocked.Timed{clock, WDL.BareBishop{}}), win)
    case 1n+rest WDL.BareKnight{}:
      Empty.absurd(P(Clocked.Timed{clock, WDL.BareKnight{}}), win)
    case 1n+rest WDL.White{kind, wk, bk, pc}:
      match win:
        case Tuple{before_50, Tuple{+next, Tuple{legal, child}}}:
          close(Clocked.Timed{clock, WDL.White{kind, wk, bk, pc}},
            (before_50, (next, (legal,
              Laws.closed_clocked_set_contains_forced_wins(
                ~P, ~close, rest,
                Clocked.next_clock(clock,
                  WDL.White{kind, wk, bk, pc}, next),
                next, child)))))
    case 1n+rest WDL.Black{kind, wk, bk, pc}:
      match win:
        case Inl{mate}:
          close(Clocked.Timed{clock, WDL.Black{kind, wk, bk, pc}},
            Inl{mate})
        case Inr{pair}:
          match pair:
            case Tuple{before_50, Tuple{has_move, replies}}:
              close(Clocked.Timed{clock, WDL.Black{kind, wk, bk, pc}},
                Inr{(before_50, (has_move,
                  (+next => legal =>
                    Laws.closed_clocked_set_contains_forced_wins(
                      ~P, ~close, rest,
                      Clocked.next_clock(clock,
                        WDL.Black{kind, wk, bk, pc}, next),
                      next, replies(next, legal)))))})

def safe_after(+n: Nat, +clock: Nat, zeroed: Bool,
  incremented: Clocked.Safe(n, 1n+clock),
  reset: Clocked.Safe(n, 0n)) ->
  Clocked.Safe(n, Clocked.next_clock.if(clock, zeroed)):
  match zeroed:
    case True{}:
      reset
    case False{}:
      incremented

def Laws.safe_unclocked_win_survives_fifty_move_rule(n, clock, game,
  safe, win):
  match n game:
    case 0n WDL.KingsOnly{}:
      win
    case 0n WDL.BareBishop{}:
      win
    case 0n WDL.BareKnight{}:
      win
    case 0n WDL.White{kind, wk, bk, pc}:
      win
    case 0n WDL.Black{kind, wk, bk, pc}:
      win
    case Succ{+rest} WDL.KingsOnly{}:
      win
    case Succ{+rest} WDL.BareBishop{}:
      win
    case Succ{+rest} WDL.BareKnight{}:
      win
    case Succ{+rest} WDL.White{kind, wk, bk, pc}:
      match safe win:
        case Tuple{before_50, Tuple{incremented, reset}}
             Tuple{+next, Tuple{legal, child}}:
          (before_50, (next, (legal,
            Laws.safe_unclocked_win_survives_fifty_move_rule(
              rest,
              Clocked.next_clock(clock,
                WDL.White{kind, wk, bk, pc}, next),
              next,
              safe_after(rest, clock,
                Clocked.zeroing(WDL.White{kind, wk, bk, pc}, next),
                incremented, reset),
              child))))
    case Succ{+rest} WDL.Black{kind, wk, bk, pc}:
      match safe win:
        case _ Inl{mate}:
          Inl{mate}
        case Tuple{before_50, Tuple{incremented, reset}}
             Inr{Tuple{has_move, replies}}:
          Inr{(before_50, (has_move, (+next => legal =>
            Laws.safe_unclocked_win_survives_fifty_move_rule(
              rest,
              Clocked.next_clock(clock,
                WDL.Black{kind, wk, bk, pc}, next),
              next,
              safe_after(rest, clock,
                Clocked.zeroing(WDL.Black{kind, wk, bk, pc}, next),
                incremented, reset),
              replies(next, legal)))))}

def ranked_zero_impossible(value: Nat,
  bounded: WDL.Truth(Nat.is_gt(value, 0n)) &
    WDL.Truth(Nat.is_le(value, 0n))) -> Empty:
  match value bounded:
    case 0n Tuple{positive, at_most}:
      positive
    case Succ{rest} Tuple{positive, at_most}:
      at_most

def ranked_evidence(~rank: WDL.Game -> Nat,
  ~cert: Ranked.BoundedCertificate(~rank), n: Nat,
  +game: WDL.Game,
  bounded: Ranked.PositiveAtMost(~rank, n, game)) ->
  Ranked.Evidence(~rank, n, game):
  match n:
    case 0n:
      bounded
    case Succ{+rest}:
      cert(rest, game, bounded)

def ranked_sound(~rank: WDL.Game -> Nat,
  ~cert: Ranked.BoundedCertificate(~rank), n: Nat,
  +game: WDL.Game, evidence: Ranked.Evidence(~rank, n, game)) ->
  WDL.WinWithin(n, game):
  match n game evidence:
    case 0n WDL.KingsOnly{} bounded:
      ranked_zero_impossible(rank(WDL.KingsOnly{}), bounded)
    case 0n WDL.BareBishop{} bounded:
      ranked_zero_impossible(rank(WDL.BareBishop{}), bounded)
    case 0n WDL.BareKnight{} bounded:
      ranked_zero_impossible(rank(WDL.BareKnight{}), bounded)
    case 0n WDL.White{kind, wk, bk, pc} bounded:
      ranked_zero_impossible(rank(WDL.White{kind, wk, bk, pc}), bounded)
    case 0n WDL.Black{kind, wk, bk, pc} bounded:
      Empty.absurd(WDL.WinWithin(0n,
        WDL.Black{kind, wk, bk, pc}),
        ranked_zero_impossible(
          rank(WDL.Black{kind, wk, bk, pc}), bounded))
    case Succ{+rest} WDL.KingsOnly{} impossible:
      impossible
    case Succ{+rest} WDL.BareBishop{} impossible:
      impossible
    case Succ{+rest} WDL.BareKnight{} impossible:
      impossible
    case Succ{+rest} WDL.White{kind, wk, bk, pc}
         Tuple{+next, Tuple{legal, child}}:
      (next, (legal,
        ranked_sound(~rank, ~cert, rest, next,
          ranked_evidence(~rank, ~cert, rest, next, child))))
    case Succ{+rest} WDL.Black{kind, wk, bk, pc} Inl{mate}:
      Inl{mate}
    case Succ{+rest} WDL.Black{kind, wk, bk, pc}
         Inr{Tuple{has_move, replies}}:
      Inr{(has_move, (+next => legal =>
        ranked_sound(~rank, ~cert, rest, next,
          ranked_evidence(~rank, ~cert, rest, next,
            replies(next, legal))))) }

def Laws.bounded_rank_certificate_is_sound(rank, cert, n, game,
  bounded):
  ranked_sound(~rank, ~cert, n, game,
    ranked_evidence(~rank, ~cert, n, game, bounded))

def nat_le_trans(a: Nat, b: Nat, c: Nat,
  ab: WDL.Truth(Nat.is_le(a, b)),
  bc: WDL.Truth(Nat.is_le(b, c))) ->
  WDL.Truth(Nat.is_le(a, c)):
  match a b c:
    case 0n _ 0n:
      Unit{}
    case 0n _ Succ{cp}:
      Unit{}
    case Succ{ap} 0n _:
      Empty.absurd(WDL.Truth(Nat.is_le(1n+ap, c)), ab)
    case Succ{ap} Succ{bp} 0n:
      Empty.absurd(WDL.Truth(Nat.is_le(1n+ap, 0n)), bc)
    case Succ{ap} Succ{bp} Succ{cp}:
      nat_le_trans(ap, bp, cp, ab, bc)

def ranked_bounded_weaken(~rank: WDL.Game -> Nat,
  +from: Nat, +to: Nat, +game: WDL.Game,
  +bound: WDL.Truth(Nat.is_le(from, to)),
  child: Ranked.PositiveAtMost(~rank, from, game)) ->
  Ranked.PositiveAtMost(~rank, to, game):
  match child:
    case Tuple{positive, small}:
      (positive, nat_le_trans(rank(game), from, to, small, bound))

def ranked_step_weaken(~rank: WDL.Game -> Nat,
  +from: Nat, +to: Nat, +game: WDL.Game,
  +bound: WDL.Truth(Nat.is_le(from, to)),
  step: Ranked.Step(~rank, from, game)) ->
  Ranked.Step(~rank, to, game):
  match game step:
    case WDL.KingsOnly{} impossible:
      impossible
    case WDL.BareBishop{} impossible:
      impossible
    case WDL.BareKnight{} impossible:
      impossible
    case WDL.White{kind, wk, bk, pc}
         Tuple{+next, Tuple{legal, child}}:
      (next, (legal,
        ranked_bounded_weaken(~rank, from, to, next, bound, child)))
    case WDL.Black{kind, wk, bk, pc} Inl{mate}:
      Inl{mate}
    case WDL.Black{kind, wk, bk, pc}
         Inr{Tuple{has_move, replies}}:
      Inr{(has_move, (+next => legal =>
        ranked_bounded_weaken(~rank, from, to, next, bound,
          replies(next, legal))))}

def ranked_local_bounded(~rank: WDL.Game -> Nat,
  +n: Nat, +game: WDL.Game, value: Nat,
  bounded: WDL.Truth(Nat.is_gt(value, 0n)) &
    WDL.Truth(Nat.is_le(value, 1n+n)),
  local: Ranked.LocalAt(~rank, value, game)) ->
  Ranked.Step(~rank, n, game):
  match value bounded local:
    case 0n Tuple{positive, at_most} Unit{}:
      Empty.absurd(Ranked.Step(~rank, n, game), positive)
    case Succ{+rest} Tuple{positive, at_most} step:
      ranked_step_weaken(~rank, rest, n, game, at_most, step)

def Laws.local_rank_certificate_implies_bounded(rank, local):
  +n => +game => bounded =>
    ranked_local_bounded(~rank, n, game, rank(game), bounded,
      local(game))

def nat_le_refl(n: Nat) -> WDL.Truth(Nat.is_le(n, n)):
  match n:
    case 0n:
      Unit{}
    case Succ{rest}:
      nat_le_refl(rest)

def Laws.local_rank_certificate_is_sound(rank, local, game, positive):
  +bound = rank(game)
  bounded = {(positive, nat_le_refl(bound)) :
    Ranked.PositiveAtMost(~rank, bound, game)}
  cert = Laws.local_rank_certificate_implies_bounded(~rank, ~local)
  (bound, Laws.bounded_rank_certificate_is_sound(
    ~rank, ~cert, bound, game, bounded))

def Laws.local_rank_certificate_wins_at_its_rank(rank, local,
  game, positive):
  +bound = rank(game)
  bounded = {(positive, nat_le_refl(bound)) :
    Ranked.PositiveAtMost(~rank, bound, game)}
  cert = Laws.local_rank_certificate_implies_bounded(~rank, ~local)
  Laws.bounded_rank_certificate_is_sound(
    ~rank, ~cert, bound, game, bounded)

def Laws.local_rank_certificate_is_clock_zero_sound(rank, local,
  game, positive, safe):
  +bound = rank(game)
  unclocked = Laws.local_rank_certificate_wins_at_its_rank(
    ~rank, ~local, game, positive)
  (bound, Laws.safe_unclocked_win_survives_fifty_move_rule(
    bound, 0n, game, safe, unclocked))

def rank_closed_at(~rank: WDL.Game -> Nat, +game: WDL.Game,
  value: Nat, zero: Ranked.ZeroClosedAt(~rank, value, game),
  attractor: WDL.Attractor(~Ranked.Positive(~rank), game)) ->
  WDL.Truth(Nat.is_gt(value, 0n)):
  match value zero:
    case 0n no_win:
      Empty.absurd(WDL.Truth(Nat.is_gt(0n, 0n)),
        no_win(attractor))
    case Succ{rest} Unit{}:
      Unit{}

def rank_closed(~rank: WDL.Game -> Nat,
  ~zero: Ranked.ZeroCertificate(~rank), game: WDL.Game,
  attractor: WDL.Attractor(~Ranked.Positive(~rank), game)) ->
  Ranked.Positive(~rank, game):
  match game:
    case WDL.KingsOnly{}:
      rank_closed_at(~rank, WDL.KingsOnly{},
        rank(WDL.KingsOnly{}), zero(WDL.KingsOnly{}), attractor)
    case WDL.BareBishop{}:
      rank_closed_at(~rank, WDL.BareBishop{},
        rank(WDL.BareBishop{}), zero(WDL.BareBishop{}), attractor)
    case WDL.BareKnight{}:
      rank_closed_at(~rank, WDL.BareKnight{},
        rank(WDL.BareKnight{}), zero(WDL.BareKnight{}), attractor)
    case WDL.White{+kind, +wk, +bk, +pc}:
      rank_closed_at(~rank, WDL.White{kind, wk, bk, pc},
        rank(WDL.White{kind, wk, bk, pc}),
        zero(WDL.White{kind, wk, bk, pc}), attractor)
    case WDL.Black{+kind, +wk, +bk, +pc}:
      rank_closed_at(~rank, WDL.Black{kind, wk, bk, pc},
        rank(WDL.Black{kind, wk, bk, pc}),
        zero(WDL.Black{kind, wk, bk, pc}), attractor)

def Laws.zero_rank_closure_is_complete(rank, zero, n, game, win):
  Laws.closed_set_contains_forced_wins(
    ~Ranked.Positive(~rank), ~rank_closed(~rank, ~zero),
    n, game, win)

def zero_cannot_be_positive(value: Nat,
  zero: WDL.Truth(Nat.is_eq(value, 0n)),
  positive: WDL.Truth(Nat.is_gt(value, 0n))) -> Empty:
  match value:
    case 0n:
      positive
    case Succ{rest}:
      zero

def zero_step_blocks_attractor(~rank: WDL.Game -> Nat,
  +game: WDL.Game, step: Ranked.ZeroStep(~rank, game),
  attracted: WDL.Attractor(~Ranked.Positive(~rank), game)) -> Empty:
  match game step attracted:
    case WDL.KingsOnly{} Unit{} impossible:
      impossible
    case WDL.BareBishop{} Unit{} impossible:
      impossible
    case WDL.BareKnight{} Unit{} impossible:
      impossible
    case WDL.White{kind, wk, bk, pc} no_win
         Tuple{+next, Tuple{legal, positive}}:
      no_win(next, legal, positive)
    case WDL.Black{kind, wk, bk, pc}
         Tuple{no_mate, escape} Inl{mate}:
      no_mate(mate)
    case WDL.Black{kind, wk, bk, pc}
         Tuple{no_mate, Inl{no_move}}
         Inr{Tuple{has_move, replies}}:
      no_move(has_move)
    case WDL.Black{kind, wk, bk, pc}
         Tuple{no_mate, Inr{Tuple{+next, Tuple{legal, zero}}}}
         Inr{Tuple{has_move, replies}}:
      zero_cannot_be_positive(rank(next), zero,
        replies(next, legal))

def zero_local_to_closed_at(~rank: WDL.Game -> Nat,
  +game: WDL.Game, value: Nat,
  local: Ranked.ZeroLocalAt(~rank, value, game)) ->
  Ranked.ZeroClosedAt(~rank, value, game):
  match value local:
    case 0n step:
      attracted =>
        zero_step_blocks_attractor(~rank, game, step, attracted)
    case Succ{rest} Unit{}:
      Unit{}

def zero_local_certificate_go(~rank: WDL.Game -> Nat,
  ~local_zero: Ranked.ZeroLocalCertificate(~rank),
  game: WDL.Game) ->
  Ranked.ZeroClosedAt(~rank, rank(game), game):
  match game:
    case WDL.KingsOnly{}:
      zero_local_to_closed_at(~rank, WDL.KingsOnly{},
        rank(WDL.KingsOnly{}), local_zero(WDL.KingsOnly{}))
    case WDL.BareBishop{}:
      zero_local_to_closed_at(~rank, WDL.BareBishop{},
        rank(WDL.BareBishop{}), local_zero(WDL.BareBishop{}))
    case WDL.BareKnight{}:
      zero_local_to_closed_at(~rank, WDL.BareKnight{},
        rank(WDL.BareKnight{}), local_zero(WDL.BareKnight{}))
    case WDL.White{+kind, +wk, +bk, +pc}:
      zero_local_to_closed_at(~rank,
        WDL.White{kind, wk, bk, pc},
        rank(WDL.White{kind, wk, bk, pc}),
        local_zero(WDL.White{kind, wk, bk, pc}))
    case WDL.Black{+kind, +wk, +bk, +pc}:
      zero_local_to_closed_at(~rank,
        WDL.Black{kind, wk, bk, pc},
        rank(WDL.Black{kind, wk, bk, pc}),
        local_zero(WDL.Black{kind, wk, bk, pc}))

def Laws.zero_local_certificate_implies_closure(rank, local_zero):
  game => zero_local_certificate_go(~rank, ~local_zero, game)

def Laws.clocked_win_implies_unclocked_win(n, clock, game, win):
  match n game:
    case 0n WDL.KingsOnly{}:
      win
    case 0n WDL.BareBishop{}:
      win
    case 0n WDL.BareKnight{}:
      win
    case 0n WDL.White{kind, wk, bk, pc}:
      win
    case 0n WDL.Black{kind, wk, bk, pc}:
      win
    case Succ{+rest} WDL.KingsOnly{}:
      win
    case Succ{+rest} WDL.BareBishop{}:
      win
    case Succ{+rest} WDL.BareKnight{}:
      win
    case Succ{+rest} WDL.White{kind, wk, bk, pc}:
      match win:
        case Tuple{before_50, Tuple{+next, Tuple{legal, child}}}:
          (next, (legal,
            Laws.clocked_win_implies_unclocked_win(rest,
              Clocked.next_clock(clock,
                WDL.White{kind, wk, bk, pc}, next),
              next, child)))
    case Succ{+rest} WDL.Black{kind, wk, bk, pc}:
      match win:
        case Inl{mate}:
          Inl{mate}
        case Inr{Tuple{before_50, Tuple{has_move, replies}}}:
          Inr{(has_move, (+next => legal =>
            Laws.clocked_win_implies_unclocked_win(rest,
              Clocked.next_clock(clock,
                WDL.Black{kind, wk, bk, pc}, next),
              next, replies(next, legal))))}

def Laws.zero_local_rank_refutes_clocked_win(rank, local_zero,
  n, clock, game, zero, clocked_win):
  unclocked = Laws.clocked_win_implies_unclocked_win(
    n, clock, game, clocked_win)
  closed = Laws.zero_local_certificate_implies_closure(
    ~rank, ~local_zero)
  positive = Laws.zero_rank_closure_is_complete(
    ~rank, ~closed, n, game, unclocked)
  zero_cannot_be_positive(rank(game), zero, positive)

def nat_le_succ_right(a: Nat, b: Nat,
  le: WDL.Truth(Nat.is_le(a, b))) ->
  WDL.Truth(Nat.is_le(a, 1n+b)):
  match a b:
    case 0n 0n:
      Unit{}
    case 0n Succ{bp}:
      Unit{}
    case Succ{ap} 0n:
      Empty.absurd(WDL.Truth(Nat.is_le(1n+ap, 1n)), le)
    case Succ{ap} Succ{bp}:
      nat_le_succ_right(ap, bp, le)

def nat_le_left_add(n: Nat, +clock: Nat) ->
  WDL.Truth(Nat.is_le(clock, Nat.add(n, clock))):
  match n:
    case 0n:
      nat_le_refl(clock)
    case Succ{+rest}:
      nat_le_succ_right(clock, Nat.add(rest, clock),
        nat_le_left_add(rest, clock))

def nat_le_add_right(n: Nat, a: Nat, b: Nat,
  le: WDL.Truth(Nat.is_le(a, b))) ->
  WDL.Truth(Nat.is_le(Nat.add(n, a), Nat.add(n, b))):
  match n:
    case 0n:
      le
    case Succ{rest}:
      nat_le_add_right(rest, a, b, le)

def pawn_single_push_advances_nat_rank(
  +pc: U32, +dest: U32,
  +bound: Laws.Truth(U32.is_lt(pc, 64)),
  same: Laws.Truth(U32.is_eq(dest,
    U32.add(pc, 8)))) ->
  Laws.Truth(Nat.is_le(
    1n+U32.to_nat(Rules.rank(pc)),
    U32.to_nat(Rules.rank(dest)))):
  +old = U32.to_nat(Rules.rank(pc))
  pushed = equality_cast(Nat,
    value => Laws.Truth(Nat.is_le(
      1n+old, value)),
    1n+old,
    U32.to_nat(Rules.rank(
      U32.add(pc, 8))),
    Equal.sym(Nat,
      U32.to_nat(Rules.rank(
        U32.add(pc, 8))),
      1n+old,
      Laws.pawn_nat_rank_after_single_push(
        pc, bound)),
    wdl_truth_to_laws_truth(
      Nat.is_le(1n+old, 1n+old),
      nat_le_refl(1n+old)))
  target = Laws.u32_equality_reflects_identity(
    dest, U32.add(pc, 8), same)
  equality_cast(U32,
    value => Laws.Truth(Nat.is_le(
      1n+old,
      U32.to_nat(Rules.rank(value)))),
    U32.add(pc, 8), dest,
    Equal.sym(U32, dest,
      U32.add(pc, 8), target),
    pushed)

def pawn_double_push_advances_nat_rank(
  +pc: U32, +dest: U32,
  +bound: Laws.Truth(U32.is_lt(pc, 64)),
  same: Laws.Truth(U32.is_eq(dest,
    U32.add(pc, 16)))) ->
  Laws.Truth(Nat.is_le(
    1n+U32.to_nat(Rules.rank(pc)),
    U32.to_nat(Rules.rank(dest)))):
  +old = U32.to_nat(Rules.rank(pc))
  pushed = equality_cast(Nat,
    value => Laws.Truth(Nat.is_le(
      1n+old, value)),
    2n+old,
    U32.to_nat(Rules.rank(
      U32.add(pc, 16))),
    Equal.sym(Nat,
      U32.to_nat(Rules.rank(
        U32.add(pc, 16))),
      2n+old,
      Laws.pawn_nat_rank_after_double_push(
        pc, bound)),
    wdl_truth_to_laws_truth(
      Nat.is_le(1n+old, 2n+old),
      nat_le_left_add(1n, old)))
  target = Laws.u32_equality_reflects_identity(
    dest, U32.add(pc, 16), same)
  equality_cast(U32,
    value => Laws.Truth(Nat.is_le(
      1n+old,
      U32.to_nat(Rules.rank(value)))),
    U32.add(pc, 16), dest,
    Equal.sym(U32, dest,
      U32.add(pc, 16), target),
    pushed)

def Laws.pawn_step_advances_nat_rank(
  pc, dest, wk, bk, bound, step):
  +single_a = U32.is_eq(dest,
    U32.add(pc, 8))
  +single_b = U32.is_ne(dest, wk)
  +single_c = U32.is_ne(dest, bk)
  +single_d = U32.is_lt(
    Rules.rank(dest), 7)
  +double_a = U32.is_eq(
    Rules.rank(pc), 1)
  +double_b = U32.is_eq(dest,
    U32.add(pc, 16))
  +double_c = U32.is_ne(
    U32.add(pc, 8), wk)
  +double_d = U32.is_ne(
    U32.add(pc, 8), bk)
  +double_e = U32.is_ne(dest, wk)
  +double_f = U32.is_ne(dest, bk)
  +single = single_a && single_b &&
    single_c && single_d
  +double = double_a && double_b &&
    double_c && double_d &&
    double_e && double_f
  or_cases(Laws.Truth(Nat.is_le(
      1n+U32.to_nat(Rules.rank(pc)),
      U32.to_nat(Rules.rank(dest)))),
    single, double, step,
    first =>
      pawn_single_push_advances_nat_rank(
        pc, dest, bound,
        first_of_four(single_a,
          single_b, single_c,
          single_d, first)),
    second =>
      +first5 = and_left(
        double_a && double_b &&
          double_c && double_d &&
          double_e,
        double_f, second)
      +first4 = and_left(
        double_a && double_b &&
          double_c && double_d,
        double_e, first5)
      pawn_double_push_advances_nat_rank(
        pc, dest, bound,
        second_of_four(double_a,
          double_b, double_c,
          double_d, first4)))

def Laws.pawn_push_preserves_budget(
  rest, pc, dest, wk, bk,
  bound, step, invariant):
  +old = U32.to_nat(Rules.rank(pc))
  +new = U32.to_nat(Rules.rank(dest))
  +middle = Nat.add(rest, 1n+old)
  +right = Nat.add(rest, new)
  middle_lower = equality_cast(Nat,
    value => Laws.Truth(Nat.is_le(
      8n, value)),
    Nat.add(1n+rest, old), middle,
    Equal.sym(Nat, middle,
      Nat.add(1n+rest, old),
      Laws.nat_add_succ_right(
        rest, old)),
    invariant)
  upper = nat_le_add_right(rest,
    1n+old, new,
    laws_truth_to_wdl_truth(
      Nat.is_le(1n+old, new),
      Laws.pawn_step_advances_nat_rank(
        pc, dest, wk, bk,
        bound, step)))
  wdl_truth_to_laws_truth(
    Nat.is_le(8n, right),
    nat_le_trans(8n, middle, right,
      laws_truth_to_wdl_truth(
        Nat.is_le(8n, middle),
        middle_lower), upper))

def Laws.legal_pawn_push_preserves_budget(
  rest, wk, bk, pc, dest,
  legal, changed, invariant):
  +from = {Rules.State{wk, bk,
    pc, 0} : Rules.State}
  +target = {Rules.State{wk, bk,
    dest, 1} : Rules.State}
  +source_valid = Rules.valid(4,
    from)
  +target_valid = Rules.valid(4,
    target)
  +same_bk = U32.is_eq(bk, bk)
  +king = U32.is_eq(pc, dest) &&
    Rules.king_step(wk, wk)
  +piece = U32.is_eq(wk, wk) &&
    Rules.piece_step(4, pc, dest,
      wk, bk)
  left = and_left(
    (source_valid && target_valid) &&
      same_bk,
    king || piece, legal)
  middle = and_left(
    source_valid && target_valid,
    same_bk, left)
  valid = and_left(source_valid,
    target_valid, middle)
  bound = state_range_pc(wk, bk,
    pc, 0,
    Laws.legal_state_squares_are_in_reverse_search_range(
      4, from, valid))
  step = Laws.legal_pawn_piece_move_is_push(
    wk, bk, pc, dest, legal,
    changed)
  Laws.pawn_push_preserves_budget(
    rest, pc, dest, wk, bk,
    bound, step, invariant)

def nat_le_to_lt_succ(a: Nat, b: Nat,
  le: WDL.Truth(Nat.is_le(a, b))) ->
  WDL.Truth(Nat.is_lt(a, 1n+b)):
  match a b:
    case 0n 0n:
      Unit{}
    case 0n Succ{bp}:
      Unit{}
    case Succ{ap} 0n:
      Empty.absurd(WDL.Truth(Nat.is_lt(1n+ap, 1n)), le)
    case Succ{ap} Succ{bp}:
      nat_le_to_lt_succ(ap, bp, le)

def nat_rotate_bound(n: Nat, clock: Nat, limit: Nat,
  bound: WDL.Truth(Nat.is_le(Nat.add(1n+n, clock), limit))) ->
  WDL.Truth(Nat.is_le(Nat.add(n, 1n+clock), limit)):
  match n limit:
    case 0n _:
      bound
    case Succ{rest} 0n:
      Empty.absurd(
        WDL.Truth(Nat.is_le(Nat.add(1n+rest, 1n+clock), 0n)),
        bound)
    case Succ{rest} Succ{remaining}:
      nat_rotate_bound(rest, clock, remaining, bound)

def safe_from_sum(n: Nat, +clock: Nat,
  +bound: WDL.Truth(Nat.is_le(Nat.add(n, clock), 99n))) ->
  Clocked.Safe(n, clock):
  match n:
    case 0n:
      Unit{}
    case Succ{+rest}:
      +inc_bound = nat_rotate_bound(rest, clock, 99n, bound)
      clock_le = nat_le_trans(clock, Nat.add(1n+rest, clock),
        99n, nat_le_left_add(1n+rest, clock), bound)
      before_50 = nat_le_to_lt_succ(clock, 99n, clock_le)
      reset_bound = nat_le_trans(Nat.add(rest, 0n),
        Nat.add(rest, 1n+clock), 99n,
        nat_le_add_right(rest, 0n, 1n+clock, Unit{}), inc_bound)
      (before_50,
        (safe_from_sum(rest, 1n+clock, inc_bound),
          safe_from_sum(rest, 0n, reset_bound)))

def Laws.plies_below_fifty_move_limit_are_safe(n, clock, bound):
  safe_from_sum(n, clock, bound)

def nat_add_zero_bound(n: Nat, limit: Nat,
  bound: WDL.Truth(Nat.is_le(n, limit))) ->
  WDL.Truth(Nat.is_le(Nat.add(n, 0n), limit)):
  match n limit:
    case 0n 0n:
      bound
    case 0n Succ{remaining}:
      bound
    case Succ{rest} 0n:
      Empty.absurd(
        WDL.Truth(Nat.is_le(Nat.add(1n+rest, 0n), 0n)),
        bound)
    case Succ{rest} Succ{remaining}:
      nat_add_zero_bound(rest, remaining, bound)

def Laws.bounded_rank_is_clock_zero_win(rank, local, game,
  positive, bound):
  +horizon = rank(game)
  sum_bound = nat_add_zero_bound(horizon, 99n, bound)
  safe = Laws.plies_below_fifty_move_limit_are_safe(
    horizon, 0n, sum_bound)
  Laws.local_rank_certificate_is_clock_zero_sound(
    ~rank, ~local, game, positive, safe)

def Laws.phase_rank_fits_fifty_move_limit(pawn, raw, bound):
  match pawn raw:
    case False{} value:
      nat_le_trans(value, 49n, 99n, bound, Unit{})
    case True{} 0n:
      Unit{}
    case True{} Succ{rest}:
      nat_le_add_right(50n, 1n+rest, 49n, bound)

def nat_le_self_add(n: Nat, c: Nat) ->
  WDL.Truth(Nat.is_le(n, Nat.add(n, c))):
  match n c:
    case 0n 0n:
      Unit{}
    case 0n Succ{cp}:
      Unit{}
    case Succ{rest} value:
      nat_le_self_add(rest, value)

def pawn_budget_at_entry_from_positive(
  rank: Nat,
  positive: Laws.Truth(
    Nat.is_gt(rank, 0n))) ->
  Laws.Truth(Nat.is_le(8n,
    Nat.add(7n, rank))):
  match rank:
    case 0n:
      match positive:
    case 1n++rest:
      wdl_truth_to_laws_truth(
        Nat.is_le(8n,
          Nat.add(7n, 1n+rest)),
        nat_le_self_add(8n, rest))

def Laws.pawn_valid_initial_budget(
  wk, bk, pc, turn, valid):
  +state = {Rules.State{wk, bk,
    pc, turn} : Rules.State}
  bound = state_range_pc(wk, bk, pc,
    turn,
    Laws.legal_state_squares_are_in_reverse_search_range(
      4, state, valid))
  ranks = Laws.pawn_valid_rank_bounds(
    wk, bk, pc, turn, valid)
  positive = pair_left(
    Laws.Truth(U32.is_gt(
      Rules.rank(pc), 0)),
    Laws.Truth(U32.is_lt(
      Rules.rank(pc), 7)),
    ranks)
  pawn_budget_at_entry_from_positive(
    U32.to_nat(Rules.rank(pc)),
    Laws.pawn_rank_positive_nat(
      pc, bound, positive))

def nat_lt_implies_le(a: Nat,
  b: Nat,
  lt: WDL.Truth(Nat.is_lt(a, b))) ->
  WDL.Truth(Nat.is_le(a, b)):
  match a b:
    case 0n 0n:
      Empty.absurd(WDL.Truth(
        Nat.is_le(0n, 0n)), lt)
    case 0n 1n+bp:
      Unit{}
    case 1n+ap 0n:
      lt
    case 1n+ap 1n+bp:
      nat_lt_implies_le(ap, bp, lt)

def Laws.pawn_zero_budget_impossible(
  wk, bk, pc, turn, valid,
  invariant):
  +state = {Rules.State{wk, bk,
    pc, turn} : Rules.State}
  bound = state_range_pc(wk, bk, pc,
    turn,
    Laws.legal_state_squares_are_in_reverse_search_range(
      4, state, valid))
  ranks = Laws.pawn_valid_rank_bounds(
    wk, bk, pc, turn, valid)
  upper = pair_right(
    Laws.Truth(U32.is_gt(
      Rules.rank(pc), 0)),
    Laws.Truth(U32.is_lt(
      Rules.rank(pc), 7)),
    ranks)
  +rank = U32.to_nat(Rules.rank(pc))
  small = Laws.pawn_rank_below_seven_nat(
    pc, bound, upper)
  nat_le_trans(8n, rank, 7n,
    laws_truth_to_wdl_truth(
      Nat.is_le(8n, rank), invariant),
    nat_lt_implies_le(rank, 7n,
      laws_truth_to_wdl_truth(
        Nat.is_lt(rank, 7n), small)))

def Laws.promotion_decreases_phase_rank(pawn_raw,
  promoted_raw, positive, promoted_bound):
  match pawn_raw:
    case 0n:
      Empty.absurd(
        WDL.Truth(Nat.is_lt(promoted_raw,
          Ranked.phase_rank(True{}, 0n))), positive)
    case Succ{+rest}:
      +middle = Nat.add(49n, 1n+rest)
      le_middle = nat_le_trans(promoted_raw, 49n, middle,
        promoted_bound, nat_le_self_add(49n, 1n+rest))
      nat_le_to_lt_succ(promoted_raw, middle, le_middle)

def Laws.lifted_rank_fits_fifty_move_limit(raw, game, bound):
  match game:
    case WDL.KingsOnly{}:
      nat_le_trans(raw(WDL.KingsOnly{}), 49n, 99n,
        bound, Unit{})
    case WDL.BareBishop{}:
      nat_le_trans(raw(WDL.BareBishop{}), 49n, 99n,
        bound, Unit{})
    case WDL.BareKnight{}:
      nat_le_trans(raw(WDL.BareKnight{}), 49n, 99n,
        bound, Unit{})
    case WDL.White{+kind, +wk, +bk, +pc}:
      Laws.phase_rank_fits_fifty_move_limit(
        U32.is_eq(kind, 4),
        raw(WDL.White{kind, wk, bk, pc}), bound)
    case WDL.Black{+kind, +wk, +bk, +pc}:
      Laws.phase_rank_fits_fifty_move_limit(
        U32.is_eq(kind, 4),
        raw(WDL.Black{kind, wk, bk, pc}), bound)

def Laws.lifted_rank_certificate_is_clock_zero_sound(raw, local,
  game, positive, raw_bound):
  lifted_bound = Laws.lifted_rank_fits_fifty_move_limit(
    ~raw, game, raw_bound)
  Laws.bounded_rank_is_clock_zero_win(
    ~Ranked.lifted_rank(~raw), ~local, game, positive,
    lifted_bound)

def nat_zero_or_positive(value: Nat) ->
  WDL.Truth(Nat.is_gt(value, 0n)) |
  WDL.Truth(Nat.is_eq(value, 0n)):
  match value:
    case 0n:
      Inr{Unit{}}
    case Succ{rest}:
      Inl{Unit{}}

def ranked_zero_clock_absurd(~rank: WDL.Game -> Nat,
  ~draws: Ranked.ZeroLocalCertificate(~rank),
  +game: WDL.Game,
  zero: WDL.Truth(Nat.is_eq(rank(game), 0n)),
  win: Clocked.ClockZeroWhiteWin(game)) -> Empty:
  match win:
    case Tuple{plies, within}:
      Laws.zero_local_rank_refutes_clocked_win(
        ~rank, ~draws, plies, 0n, game, zero, within)

def clock_zero_black_absurd(+game: WDL.Game,
  win: Clocked.ClockZeroBlackWin(game)) -> Empty:
  match win:
    case Tuple{plies, within}:
      Laws.black_cannot_force_clocked_win(plies, 0n, game,
        within)

def ranked_classify(~rank: WDL.Game -> Nat,
  ~wins: Ranked.LocalCertificate(~rank),
  ~draws: Ranked.ZeroLocalCertificate(~rank),
  +game: WDL.Game,
  bound: WDL.Truth(Nat.is_le(rank(game), 99n)),
  decided: WDL.Truth(Nat.is_gt(rank(game), 0n)) |
    WDL.Truth(Nat.is_eq(rank(game), 0n))) ->
  Ranked.ExactClockZero(~rank, game):
  match decided:
    case Inl{+positive}:
      Inl{(positive,
        Laws.bounded_rank_is_clock_zero_win(
          ~rank, ~wins, game, positive, bound))}
    case Inr{+zero}:
      Inr{(zero, (win =>
        ranked_zero_clock_absurd(~rank, ~draws, game, zero, win),
        black => clock_zero_black_absurd(game, black)))}

def Laws.local_certificates_give_exact_clock_zero_wdl(rank,
  wins, draws, game, bound):
  ranked_classify(~rank, ~wins, ~draws, game, bound,
    nat_zero_or_positive(rank(game)))
