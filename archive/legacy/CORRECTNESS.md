# Correctness status and argument

## Current proof-first generator (in progress)

`main.bend` now writes the clocked dynamic-programming tables from
`src/clocked_tables.bend`, not the older rank/queue solver described below.
For arbitrary symbolic path trees, `PROOF.bend` proves by induction that the
queen and rook clock layers agree with the independent scalar
`Minimax.value` recursion, and that all pawn clock and push-budget layers
agree with `Exact.value`. The proof covers White king moves, White piece
moves, Black's universal replies, queen/rook promotion, the 100-halfmove
draw boundary, and the bitwise table index. It never evaluates all positions.
Separate Bend lemmas establish that a valid pawn starts with enough budget,
every legal pawn push preserves the rank-plus-budget invariant, and no valid
pawn position can be reached with zero budget. The new entry point writes
the resulting tree bytes directly to five separate files. Generic full-tree
and serialized-length lemmas prove the intended tree shape and byte count.

This is **not yet a complete correctness proof**. The outstanding bridge is
from the direct Boolean minimax recursions, together with their pawn-budget
invariant and square-list completeness, to the independent quantified
perfect-play `Clocked.WinWithin` semantics for all legal states. A checked
structural theorem now ties each serialized byte at a tree-path offset to
its certified minimax value; the arithmetic equivalence of that offset to
the documented integer index still needs a separate lemma. Existing
`build/*.wdl` files predate this generator and have not been regenerated
from it. The five-second checker target remains unmet
(currently about 15 seconds). Nothing below should be read as closing these
gaps.

## Legacy rank/queue approach

The requested fully formal Bend proof of the generated WDL values is **not yet
complete**. The solver no longer stores an unresolved-successor counter.
Whenever a Black predecessor is reconsidered, it scans a structurally
generated list of all 64 candidate destinations, marks the position only if at least one legal move exists and
every legal move is a previously marked noncapture White win, and assigns one
plus the maximum successor rank. This avoids a mutable-counter invariant.
`PROOF.bend` proves by induction over an arbitrary scan length that the scan's
`all_won` flag implies each examined legal reply is a positive-rank
noncapture, and conversely that those conditions preserve `all_won`. It also
proves that an examined legal reply sets `seen`, and that the initial-mate
Boolean scan detects legal moves in the list. A separate induction over
six-bit words proves every square below 64 belongs to this list. For any
solver work state whose square-list invariant holds, Bend combines those
results to prove that a legal Black move is detected and that `all_won`
constrains every legal reply. The list is created once in `Retro.new`, carried
through mate seeding and the queue/retrograde loops, and its coverage is
preserved by symbolic induction over arbitrary loop lengths. The checker
does not expand the concrete 64- or 524,288-step runs into a position scan.
Older abstract counter lemmas remain in
`src/retrograde_logic.bend`, but are not a refinement proof for the current
solver. The formal attractor clauses are monotone: adding
known White wins cannot undo an established win; the Black clause distinguishes
checkmate from stalemate when there are no moves. `src/wdl_spec.bend` defines
finite-horizon winning for an explicit-turn chess game, with promotion as a
material-changing move and capture into K vs K as a non-winning exit.
Its no-legal-move premise is quantified, not computed by scanning 64 squares.
`src/clocked_step.bend` now expresses one clock-aware Bellman step, including
the stipulated draw at halfmove clock 100. For an arbitrary square list with
a structural coverage proof, Bend proves that its Black checkmate test is
equivalent to the quantified chess checkmate rule. It also proves both
directions of the White king and piece scans: a positive scan yields a legal
winning-destination witness, and any such listed destination is found. The
actual six-bit square list has a separate structural coverage theorem, so
these proofs do not evaluate concrete board positions in the checker.

`src/finite_wdl_spec.bend` is a proof-oriented finite-horizon game semantics.
Black's universal move condition is represented as a structural product over
legal destination squares. Bend's affine function quantifier in the older
specification cannot be duplicated to derive all scanner obligations, whereas
the product can be split by list induction. This new semantics is not yet
connected to the generator or saved files.
`PROOF.bend` proves that K vs K cannot be a finite-horizon White win (nor a
`WhiteCanForceWin` witness) and that increasing the horizon preserves an
existing forced win. It proves that a legal Black capture into K vs K rules
out a finite-horizon White win, and that a legal black king move cannot leave
the kings adjacent. These proofs do not enumerate positions.

`src/proof_tree.bend` is a proof-first persistent alternative to Bend's affine
`Array`. The Bend laws prove, for arbitrary bit indices rather than enumerated
table entries, that a write reads back its value, that a filled tree reads as
filled, that writes preserve full-tree shape, and that writing one index leaves
every different index unchanged. This is the start of a simpler route to a
solver refinement proof. The retrograde solver now uses this tree for its
`won` map, then converts the finished `won` tree to an
`Array` for checking and writing. Its queue is now a persistent two-list FIFO;
Bend laws prove that pushing appends to its logical contents and popping
reassembles those contents in FIFO order, and that an empty pop means the
logical queue is empty, using generic list inductions.
Further laws show that actual `Retro.mark.new` preserves full depth-19 tree
shape for arbitrary work states satisfying that invariant. Its write and
unchanged-field behavior is proved; `mark.rank` has a proved conditional rank
and FIFO-append rule, and `Retro.take` has a proved FIFO-pop rule. For any tree, Bend also
proves that converting it to the output array preserves the entire serialized
byte sequence, without enumerating entries. These laws do **not** yet prove
the complete solver transitions or that the tree's bytes are correct WDL.
The checker currently takes roughly 4.7 seconds, above the two-second goal in
`AGENTS.md`.

The `closed_set_contains_forced_wins` law additionally proves, for any
proposition on game positions, that closure under the one-ply White-win
attractor contains every finite-horizon White win. It is the symbolic
completeness argument for retrograde propagation, conditional on proving the
actual queue reaches such a closed set.

`src/clocked_wdl_spec.bend` adds the halfmove clock to the semantic model.
Per the requested tablebase convention, clock 100 is a terminal draw rather
than an optional claim: the defender claims it under perfect play. Checkmate
on the move reaching 100 has already ended the game and takes precedence.
The Bend laws establish that boundary, checkmate, stalemate,
and the K+B vs K and K+N vs K dead-material exits symbolically. The
`material_game` mapping now treats every KBK/KNK position, not only a newly
promoted one, as a terminal insufficient-material draw. Their tables are
constructed directly as zero arrays, preserving the bytes previously
produced by retrograde search. A generic induction over array depth proves
that every read from `Array.new(U32, depth, value)` returns `value`, including
the depth-19 zero arrays, without expanding the 524,288 leaves in the proof.
The serializer now flattens arrays structurally in left-to-right order.
Further generic Bend inductions prove that flattening a uniform zero array
emits only zero values and that flattening a uniform array of depth `d` emits
`2^d` values, without evaluating a concrete depth-19 list. A separate
binary-U32 arithmetic law checks that depth 19 has 524,288 slots. The proof
packages these array facts with the terminal-draw semantics into symbolic
correctness theorems for every KBK and KNK array entry. It still needs a
bridge from flattening to the IO writer, and proofs for the nonuniform
generated tables. The laws
check in a few seconds; the earlier multi-minute checker time came from a
64-square move count inside the proof specification, which has been removed.
The `closed_clocked_set_contains_forced_wins` law proves the same symbolic
attractor-completeness result for the clocked game, including zeroing moves
and the 100-halfmove draw boundary. It is independent of the number of board
positions.
The `safe_unclocked_win_survives_fifty_move_rule` law converts any unclocked
finite-horizon strategy into a clocked one when supplied with a structural
budget covering both a nonzeroing move and a clock reset at every ply.
`plies_below_fifty_move_limit_are_safe` now derives that budget from a
numeric bound: horizon plus starting clock at most 99. This is proved by
induction on natural numbers, not by evaluating chess positions or clock
histories.

`src/rank_spec.bend` now states the rank-certificate rule for an *arbitrary*
function from game positions to natural-number ranks. In `PROOF.bend`,
`local_rank_certificate_implies_bounded` proves that a smaller positive
successor rank satisfies the corresponding horizon obligation;
`local_rank_certificate_wins_at_its_rank` then proves by induction that every
positive-rank position is a White win within its rank in plies. The theorem
quantifies over positions and does not enumerate them. A further law lifts
that win to the clock-zero game from a global rank bound of 99. Pawn-table
ranks get a phase offset of 50 on positive entries, so every promoted-piece
rank bounded by 49 is strictly lower; the lifted pawn rank remains at most 99.
The `zero_rank_closure_is_complete` law separately proves that a zero-entry
set closed against the White-win attractor contains no finite forced wins.
`zero_local_certificate_implies_closure` now derives that closure from a
checker-shaped local rule: White cannot move from zero to a positive rank;
Black is not mated and either has no legal move or has a zero-rank reply.
`clocked_win_implies_unclocked_win` shows that clock restrictions cannot
create a win, so `zero_local_rank_refutes_clocked_win` rules out clocked wins
at zero entries. Separate Bend laws define Black's finite-horizon forcing
semantics, both with and without the halfmove clock, and prove by induction
that the lone Black king cannot force a win from any position. They use the
symbolic fact that a legal White-to-move state cannot have White in check.
The resulting `local_certificates_give_exact_clock_zero_wdl` law packages
the abstract classification: positive rank has a clock-zero White win; zero
rank has neither a White win nor a Black win. This still assumes the local
certificate premises; it does not prove the generated arrays meet them.
For the concrete queue, two further laws show that every legal same-class
White or Black move has the source-component shape searched by the
corresponding predecessor loop. Another law proves every square in a legal
state is in that loop's `0..63` range. A symbolic induction over `Word` bits
proves `U32.is_eq(x, x)` for arbitrary `x`, allowing further laws to prove
that `Rules.move_to` same-class edges and the explicit-turn WDL game's
same-material moves coincide in both directions. The converse proof also
reflects bitwise U32 equality into propositional identity, to exclude the
spurious case of treating a pawn-to-pawn move as a promotion. The Black
capture-to-K-vs-K exit also coincides with the formal game's draw exit in
both directions. Pawn seeding and the formal promotion relation now share
`Rules.pawn_can_promote`; symbolic laws prove every semantic promotion has
that seed shape, that a seed with a legal promoted target is a semantic
promotion, and that queen/rook promotions are game edges exactly when the
promotion predicate holds. Bishop/knight promotions lead to the dead-material
draw exits. The remaining promotion obligation is to prove the generator's
four target-table reads and winner aggregation exactly match these edges.
The predecessor loops now traverse the same complete square list; their
state-shape laws are proved, but a full theorem connecting the loop updates
to every legal edge is still missing. A further Boolean
proof shows a legal White same-class move cannot leave both its king and
extra-piece square unchanged; hence the king-source and piece-source
predecessor scans cannot both count the same legal edge.
An additional symbolic law proves that every legal Black king destination is
within the 64-square scan: a capture uses the valid original piece square,
while a noncapture uses the validity of the destination state.
As a foundation for the encoding proof, `src/encoding.bend` expresses the
19-bit layout by structural `Word` append/split operations. Bend proves both
generic append/split inverse laws and the structural encoder's round trip
without enumerating indices. The executable encoder remains the faster U32
mask/shift/or version. Bend now also proves, for arbitrary U32 square and turn
inputs, that the executable `Rules.index` equals the structural encoder. This
uses symbolic proofs for the masks, the three shifts, and merging four
disjoint bit fields, not a scan of index values. Bend also proves that
`Rules.decode(Rules.index(state))` returns the canonical low-six-bit square
fields and low-one-bit turn for arbitrary U32 fields. More strongly, the
executable `Rules.decode` equals the structural decoder for every 32-bit
input, including out-of-range table indices. The decoder argument uses a
generic symbolic shift/drop theorem and a symbolic 32-bit split/repack proof,
not a scan of indices. Bend proves that `Rules.valid` implies each square is
below 64 and the turn is below 2, and that these bit bounds make the canonical
state equal to the original. Thus `Rules.decode(Rules.index(state)) == state`
for every valid state. It also proves
`Rules.index(Rules.decode(i)) == i & 524287` for every U32 index, exactly the
mask used by the depth-19 array operations.
These are conditional theorems: they do **not** establish that the solver's
`won` tree satisfies the universal positive-rank and zero-closure premises.

The former generator relied on a runtime certificate check.
`src/retrograde.bend` constructs ranks; `src/certificate.bend` traverses every
index and checks those ranks against the legal successor relation.
`verify.bend` independently reads the five saved files and checks that old
certificate format. These modules are retained for comparison but are not
called by the current proof-first `main.bend`.

The stored entries are interpreted from halfmove clock zero. A successful
certificate is also required to have raw rank at most 49 in every class.
The Bend arithmetic proof establishes that the phase-lifted rank is at most
99, so a positive entry satisfying the *symbolic* local-rank premise wins
before the clock boundary. What remains unproved is that the concrete entries
do satisfy that premise. The requested terminal-draw convention differs from
the literal
[FIDE rules](https://handbook.fide.com/chapter/e012023), where the 50-move draw
is claimable rather than automatic.

The remaining formal obligations are to prove the Black scan's maximum is the
maximum legal reply rank without overflow, connect mate seeding and the
predecessor updates to a global invariant on the persistent `Work.won` tree
and FIFO queue, prove every legal predecessor is updated, prove queue
exhaustion gives the least fixed point,
establish the universal positive-rank and rank-zero closure premises for the
tree and its converted array output and saved bytes,
connect the decoded U32 turn to the explicit-turn WDL game model,
and prove the move relation is equivalent to the intended chess rules,
including capture and promotion exits. Until then, `bend PROOF.bend` passing
must not be read as certification of the WDL bytes.

## Coverage and rules

For each of the five piece classes, an index is the mixed-radix encoding of
three square numbers in `[0, 63]` and a turn in `{0, 1}`. There are
`64 * 64 * 64 * 2 = 524,288` indices per class. `Rules.valid` excludes
overlapping pieces, adjacent kings, pawns on their first or eighth rank, and
states in which the side that just moved (Black, when White is to move) is in
check. The move relation enumerates every target square for a king or extra
piece. Slider rays are blocked by either king. A pawn may push once, push twice
from its starting rank if both squares are empty, or promote to any of the four
pieces. A lone king may capture an undefended extra piece, entering drawn K vs
K. Checkmate and stalemate are distinguished by whether the black king is in
check when it has no legal moves.

All five normalized classes cover three-man material: Q, R, B, N, or P plus
two kings. Reflecting ranks and swapping colors maps Black-extra-piece states
to these White-extra-piece states while preserving legal moves and WDL.

## Certificate conditions

Let rank zero mean draw and a positive rank mean White wins. The certificate
checker verifies these statements for every valid state; invalid states must
have rank zero:

1. At a positive-rank White turn, at least one legal move reaches a smaller
   positive rank. A winning pawn promotion is also accepted, after the
   promoted-piece tables have been certified.
2. At a positive-rank Black turn, either the position is checkmate at rank one
   or every legal move reaches a smaller positive rank. A capture of the extra
   piece fails this condition because K vs K is drawn.
3. At a zero-rank White turn, no legal move reaches a positive rank and no
   promotion reaches a winning promoted-piece position.
4. At a zero-rank Black turn, a legal move reaches rank zero, the extra piece
   can be captured, or there are no legal moves and Black is not in check.

The checker inspects all 524,288 indices in each class. It checks the four
promotion-independent classes first and then KPK. Each positive rank is stored
as one byte; values above 255 would make file writing fail.

## Why the conditions imply WDL

For a positive rank, use induction on the rank. White chooses the certified
smaller-rank move; every Black response has a smaller rank. Natural numbers
cannot decrease indefinitely, so play reaches checkmate, or a pawn promotes
into an already certified winning table. White can therefore force a win.

For rank zero, Black can always choose a rank-zero continuation, capture the
extra piece for a draw, or accept stalemate. White has no move into a certified
win. This gives Black a strategy to avoid defeat forever or reach a draw. A
lone black king cannot checkmate the white king in a legal three-man state, so
rank zero is a draw rather than a Black win. Promotion dependencies are acyclic:
the four non-pawn classes are certified before KPK.

Thus each byte *that satisfies the certificate conditions* gives the exact WDL
result under the encoded rules. The checker and `Rules` remain trusted code;
Bend checks their types and termination, but this implication and the link from
the solver to the conditions are still prose, not complete Bend laws. The
result is conditional on those definitions matching chess, the Bend
compiler/runtime, and the stated clock and castling conventions.
