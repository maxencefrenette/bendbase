# Bendbase

A Bend 2 WDL tablebase project with generators for three-man tables (KQK, KRK,
KBK, KNK, KPK) and pawnless four-man tables. Correctness proofs also cover
four-man tables with pawns, which do not yet have optimized generators.
Each table includes both color reversals and either side to move.
Queries start at halfmove clock zero. Castling rights are excluded.

The complete correctness theorem is in [LAWS.bend](LAWS.bend). It connects
the bytes produced by the generator to perfect-play strategies under the
specified chess rules, in both directions for both players. Run:

```sh
mise install
mise exec -- bend PROOF.bend
```

The proof is structural and does not enumerate chess positions. The current
checker run takes about 1.2 seconds on this container. The comments in
[LAWS.bend](LAWS.bend) document the theorem's scope and execution boundary.

## Pawnless four-man proof

`src/material_chess.bend` provides material-independent pawnless positions and
move rules: two kings plus a list of colored pieces, with full-board obstruction,
captures, and king safety. `PROOF.bend` checks move-generation completeness and
soundness, successor validity, and lossless conversion from three-man boards.
The move domain is all 12-bit source/destination pairs; the proof keeps this
domain symbolic rather than checking individual positions.

The proof now covers every pawnless four-man material configuration, both
ownership relations, both colors, and both sides to move. It connects the
clock-layer generator's serialized WDL bytes directly to perfect-play strategies
under the chess game semantics. Captures enter the three-man game with a fresh 100-halfmove allowance;
quiet moves consume one halfmove. Structural proofs establish that captures
reduce material and quiet moves preserve it. The three-man continuation uses
the same generalized rules, without assuming equivalence to the old solver.

`four_index.Material` specifies the two piece kinds and whether they have
opposing owners. Its file has a 26-bit index and one signed byte
per slot (64 MiB). The high six bits encode the second piece's square; the
low twenty bits use the existing three-man layout for the first piece and
kings. Thus `offset = second_square * 1048576 + three_man_offset`.
Invalid placements are outside the WDL theorem's domain.

No four-man tables have been generated during development, and `main.bend`
still generates only the five three-man files. There is no separate four-man
reference solver: `four_chess.bend` defines the rules/game tree, and the generator
is proved correct against that specification. Three-man and pawnless four-man
generation share the engine described below; their chess specifications remain
independent and their full correctness laws are unchanged.

## Shared generation engine

`src/clock_solver.bend` now owns the actual reversible-clock solver used by
pawnless three-man, KPK, and pawnless four-man generation. Each compiles a
component graph with terminal nodes, quiet edges (same-table keys), and reset
edges (completed dependency outcomes). The solver has no material-family cases.
`src/table_engine.bend` supplies parallel indexed filling, WDL folding and byte
conversion; it no longer contains a separate clock iteration implementation.
`src/table_engine_proof.bend` proves indexed filling and byte conversion once,
by structural induction, and the adapters reuse those results in their WDL proofs.

`src/dependency_engine.bend` owns parallel dependency-family construction,
ordered component scheduling, and completed-cache lookup. Both promotion and
capture dependencies are built from ordinary descriptor families: the separate four-field
`Promotions`/`Bundle` containers and selectors have been removed. KPK now uses
the common scheduler and list cache instead of its own rank datatype, recursive
schedule, and cache traversal. These operations are generic over payload types,
not limited to a fixed piece count or table width. Structural proofs establish
family lookup, exact schedule length, and preservation of every completed stage.

`src/table_cache.bend` stores completed tables with their own runtime index
widths, so one family or history can contain different-sized components. Capture,
promotion, pawn-push and final KPK rank lookups all use the same exact-width reader.
Its structural proofs show both that matching keys return the stored value and
that successful reads cannot have mismatched widths. Keys are never padded or
truncated by this cache. Existing WDL proofs show the adapters select the right
entries and do not take the width-mismatch fallback during valid generation.

`src/material_cache.bend` selects those entries by their full ordered material
signature, including every piece kind and relative owner. Executable capture and
promotion lookups use this directory instead of fixed Q/R/B/N cache-slot indices.
The same reader accepts general `position_address.Address` values. Structural
proofs establish exact signature matching, that every hit names an actual matching
entry, and lossless reads of registered common-address tables. Missing signatures
remain `None`; no table or material class is assumed to exist.

`src/component_cache.bend` adds an explicit stage identifier to each completed
material directory. KPK uses it for single pushes, double pushes and final rank
reads; the old list-offset selection and `5 - rank` calculation are removed.
The common scheduler assigns stage labels itself, and structural proofs establish
that its completed cache contains only earlier stages. A newer stage cannot
shadow a requested older component, and the current stage cannot be read from
that earlier-stage cache. The staged reader also accepts common N-men addresses.

Adapters retain their move rules, indexing, and choice of dependency strata.
Captures read completed lower-material tables. KPK solves ranks nearest promotion first,
so pawn pushes and promotions read completed tables at a fresh clock, while quiet
moves read the previous clock layer. Its final rank selection also uses the
shared indexed fill. Structural compilation proofs connect each graph to the
existing chess semantics, preserving all end-to-end WDL laws. The component
solver also has a general serialized-byte/strategy theorem independent of
material. Graphs are currently held in memory: this avoids regenerating moves
at every clock but increases memory use; no performance claim is made.

Cache misses are explicit `None` values. Legacy adapters supply explicit draw
fallbacks where their existing chess proofs justify them; the general cache does
not assign WDL outcomes to missing dependencies.

This consolidates clock solving and scheduling machinery, not the whole chess pipeline.
Graph builders still own legacy move rules, indexing and chess-specific routing.
The common scheduler executes a supplied order. Stage-and-material reads are implemented and used by
KPK. `src/chess_measure.bend` defines the common stage measure as total men
plus the sum of pawn ranks remaining to promotion. The common pawn rules express
forward displacement using this same coordinate. Structural proofs establish
that legal resets strictly decrease this measure and legal quiet moves preserve
it. `src/chess_selection_proof.bend` connects move selection to the actual list
updater, with no extra pawn-progress premise. Combining the measure and the clock
as `(limit + 1) * measure + remaining` gives a bound decreasing on every legal
continuation, including common graph address and clock routing. At limit 100,
this includes capture/pawn-move clock resets, promotions, and en passant.
`src/chess_component_proof.bend` also proves that legal quiet moves preserve
the ordered material signature, including relative ownership, and that their
actual routed addresses stay in the same material/measure component with the
same key width. This establishes quiet-component closure without enumerating
positions. `src/chess_cache.bend` derives reset stages directly from destination
positions and produces shared clock-solver reset edges, retaining explicit
failure for missing dependencies. Its proof establishes that every legal reset
finds its stage in a sufficiently completed schedule, for any component builder,
and that a registered exact-width material table returns its exact stored value.
This proves stage coverage, not material-directory completeness or correctness
of those stored WDL values. Material coverage, full component compilation, and
the global WDL composition are still pending.
A material signature alone does not identify a rank-specific component; the
common measure is not yet wired into production stage selection.
Pawnful four-man byte lists still use the game evaluator.

### Toward an N-men solver

`src/position.bend` defines one material signature and board representation for
any number of non-king pieces. Kinds include pawns and Q/R/B/N; ownership is
relative to a per-position anchor color. Kings, turn and explicit en-passant
state are common to every material. Ordered slots also support identical pieces.

`src/position_index.bend` provides one recursive index, with six bits per extra
piece and a 21-bit frame. Structural proofs establish lossless decoding and
injectivity for arbitrary piece counts, without enumerating positions.
`src/position_legacy.bend` supplies proved lossless three-/four-man board
conversions and position-preserving embeddings for pawnless tables and KPK.

`src/chess.bend` implements common move rules over these positions: arbitrary
piece lists, all promotions, double pushes, captures and en passant. Move
enumeration is proved complete and sound, and successors preserve validity.
It also supplies terminal detection and a common clock-reset predicate.

`src/position_address.bend` derives a runtime-sized material signature and key
from any common position, without a material-family switch. Its address round-trip
and non-aliasing proofs cover arbitrary piece lists, promotions and EP state.
`src/chess_graph.bend` builds unresolved quiet/reset edges with these addresses.
A structural proof shows that decoding its graph preserves every successor and
terminal result of the common chess rules; separate laws preserve the clock policy.
Reset edges remain addresses until their dependencies are resolved, so a missing
dependency cannot be mistaken for a draw at this stage.

The remaining work is to schedule these address reads under a proved dependency
order, prove conversion of legacy move rules, and migrate the file generators
to the common graph and index (their material-cache reads are already shared).
The common graph builder is not yet used by those generators. Its move/graph
proofs and the component solver theorem are NOT a completed N-men chess WDL proof.
Existing file formats remain unchanged. No speed or compactness claim is made
for the new internal index; stored roots will exclude EP rights even though
continuation states retain them.

## Generate pawnless four-man tables

`four_main.bend` is a separate, opt-in executable. With the output directory
already created:

```sh
mkdir -p build
mise exec -- bend four_main.bend -o build/bendbase-four
./build/bendbase-four -- --help

# KQRK: both extras belong to the same player.
./build/bendbase-four -- q r same build/kqrk.wdl

# KQKR: the extras belong to opposing players.
./build/bendbase-four -- q r opposed build/kqkr.wdl

# All 20 canonical pawnless four-man material configurations.
./build/bendbase-four -- --all build
```

Kinds are lowercase `q/r/b/n`; either order is accepted for a single table.
Keep that order when encoding its positions. Batch generation uses Q, R, B, N
order, includes both color reversals in each file, and shares its three-man
capture dependencies across files. Each output is 64 MiB, one signed byte per
26-bit slot. Existing output files are overwritten. No arguments just prints help.
The first `--` separates Bend runtime options from generator arguments.

The generator computes a terminal layer followed by 100 reversible-clock layers.
Each layer reads previously solved positions instead of recursively evaluating
their game trees. Captures consult completed three-man tables at a fresh clock.
Those dependencies use the same generalized move rules as the chess semantics, rather
than assuming equivalence with the older three-man implementation. Table halves
are built in parallel; preceding layers are shared during each sweep.

The law `generated_pawnless_four_wdl_is_fully_correct` proves serialized-byte
correctness directly. Induction relates each cached clock layer to the legal
game tree, then the generic strategy theorem establishes WDL. No intermediate
solver-equivalence theorem is needed. The proof also establishes that move transitions
preserve the piece kinds and ownership needed for correct cache lookup.

This is an executable dynamic-programming implementation, **not a demonstrated
Syzygy-speed generator**. Full generation time and peak memory have not been
measured. It still uses dense tree-shaped tables and the generalized move scan;
faster move enumeration, compact storage, and benchmarking remain future work.

## Four-man positions with one pawn

The proof also covers two kings, exactly one pawn, and one queen, rook, bishop,
or knight, with either ownership relation and either pawn color. The rules
include pawn captures, single/double pushes, all four promotions (including
capture-promotions), and post-move king safety with every blocker accounted for.

Quiet king/piece moves consume the clock. Pawn moves and captures reset it.
Capturing the extra piece enters KPK; capturing the pawn enters pawnless
three-man chess; promotion enters pawnless three- or four-man chess. The proof
decreases actual pawn distance and then remaining clock, with lower-material
and pawnless continuations handled by the existing game definitions.

`one_pawn_tables.Profile` specifies the non-pawn kind and whether its owner
opposes the pawn. The byte layout is the same 26-bit layout above,
with the pawn as the first piece and the extra piece as the second. The public
law `one_pawn_four_wdl_is_fully_correct` certifies the serialized WDL bytes in
both directions for both players, without enumerating positions.

The one-pawn byte-list definition uses the generic game evaluator directly,
without a separate one-pawn solver. An optimized generator remains future work;
the executable supports only pawnless four-man tables. Proof checking generates
no tables.

## Four-man positions with two pawns

The proof now includes KPPK and KPKP, completing the four-man material classes.
Both pawn colors, ownership relations, and sides to move are covered. It includes
single/double pushes, captures, all four promotions, and en passant with immediate
expiry and post-capture king safety. Captures enter KPK; promotions enter the
one-pawn game. Termination follows the two actual pawn distances, then the clock.

To keep the implementation small, the table definition uses the existing generic
minimax evaluator directly and reuses the 26-bit index. `two_pawn_tables.Profile`
contains only `opposed`: false for KPPK, true for KPKP. Each specified file has
one byte per slot (64 MiB), with the same encoding as the other four-man files.
The law `two_pawn_four_wdl_is_fully_correct` connects those serialized bytes to
perfect-play strategies in both directions, alongside move soundness,
completeness, successor safety, and exact file-length proofs.

Stored roots have halfmove clock zero **and no en passant right**. These are
separate restrictions: a double push resets the clock to zero, too. En passant
is fully included during calculation after subsequent double pushes, but an
initial position with an en passant right cannot be looked up in these files.
The two-pawn implementation remains a slow specification-level definition, not an
executable dynamic-programming generator.
No four-man tables are generated during proof checking or by `main.bend`.

## Generate

The repository pins Clang through mise. With Bend installed:

```sh
mkdir -p build
mise exec -- bend main.bend -o build/bendbase
./build/bendbase
```

The generator writes five files in `build/`. Pawnless tables use 100 clock
layers. KPK solves each pawn rank at all clocks, starting nearest promotion;
pawn pushes use completed rank tables at a fresh clock, and promotions use
the pawnless tables. Both colors and all four promotion choices are included.
This implementation prioritizes the proof; full table generation has not yet
been run or benchmarked. Obsolete tables from the earlier implementation have
been removed.

## File format

Each three-man file has 1,048,576 entries, one signed byte per encoded position
(four-man files have 67,108,864 entries):

| Byte | Meaning |
| --- | --- |
| `1` | White can force a win |
| `0` | Draw under perfect play |
| `-1` (`0xFF`) | Black can force a win |

Squares use `a1 = 0` through `h8 = 63`. The 20-bit key, most significant bit
first, concatenates `owner`, `turn`, `piece[5..0]`, `black_king[5..0]`, and
`white_king[5..0]`. Owner and turn use `0` for White and `1` for Black.
Its ordinary binary value is the byte offset:

```text
offset = white_king + 64 * black_king + 4096 * piece
       + 262144 * turn + 524288 * owner
```

The formal offset is `Finite.offset(20n, Index.encode(board))`. The file names
are `kqk.wdl`, `krk.wdl`, `kbk.wdl`, `knk.wdl`, and `kpk.wdl`. These are simple custom WDL
files, not Syzygy-compatible files. Invalid placements occupy zero-valued slots;
callers must apply `Chess.valid` (pawnless) or `Pawn.valid_board` (KPK) before
interpreting an entry as a chess result. KPK uses the pawn square as `piece`;
unpromoted pawns on the first or eighth rank are invalid.

Checkmate takes precedence on the move reaching 100 halfmoves. Otherwise that
boundary is a terminal draw, following the agreed tablebase convention.
Stalemate, insufficient material, and captures leaving K vs K are draws.
Every pawn move, including promotion, resets the halfmove clock to zero.
The files do not store arbitrary nonzero halfmove clocks or repetition history.
