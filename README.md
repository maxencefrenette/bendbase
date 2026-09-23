# Bendbase

A Bend 2 WDL tablebase project with generators for three-man tables (KQK, KRK,
KBK, KNK, KPK) and pawnless four-man tables. Correctness proofs also cover
four-man tables with pawns, whose implementations remain reference-only.
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
ownership relations, both colors, and both sides to move. It connects a pure
reference minimax recurrence to perfect-play strategies and to serialized WDL
bytes. Captures enter the three-man game with a fresh 100-halfmove allowance;
quiet moves consume one halfmove. Structural proofs establish that captures
reduce material and quiet moves preserve it. The three-man continuation uses
the same generalized rules, without assuming equivalence to the old solver.

`four_index.Material` specifies the two piece kinds and whether they have
opposing owners. Its reference file has a 26-bit index and one signed byte
per slot (64 MiB). The high six bits encode the second piece's square; the
low twenty bits use the existing three-man layout for the first piece and
kings. Thus `offset = second_square * 1048576 + three_man_offset`.
Invalid placements are outside the WDL theorem's domain.

No four-man tables have been generated during development, and `main.bend`
still generates only the five three-man files. The reference recurrence is not
memoized; it remains the specification for the executable clock-layer generator
described below. Existing three-man generators and proofs are intact.

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
Those dependencies use the same generalized move rules as the reference, rather
than assuming equivalence with the older three-man implementation. Table halves
are built in parallel; preceding layers are shared during each sweep.

The laws `pawnless_four_generator_matches_reference` and
`generated_pawnless_four_wdl_is_fully_correct` prove pointwise equivalence and
serialized-byte correctness. The proof also establishes that move transitions
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
opposes the pawn. The reference byte layout is the same 26-bit layout above,
with the pawn as the first piece and the extra piece as the second. The public
law `one_pawn_four_wdl_is_fully_correct` certifies the serialized WDL bytes in
both directions for both players, without enumerating positions.

The one-pawn extension remains reference/proof-only; the new executable supports
only pawnless four-man tables. Proof checking does not generate any tables.

## Four-man positions with two pawns

The proof now includes KPPK and KPKP, completing the four-man material classes.
Both pawn colors, ownership relations, and sides to move are covered. It includes
single/double pushes, captures, all four promotions, and en passant with immediate
expiry and post-capture king safety. Captures enter KPK; promotions enter the
one-pawn game. Termination follows the two actual pawn distances, then the clock.

To keep the implementation small, the reference table uses the existing generic
minimax evaluator directly and reuses the 26-bit index. `two_pawn_tables.Profile`
contains only `opposed`: false for KPPK, true for KPKP. Each reference file has
one byte per slot (64 MiB), with the same encoding as the other four-man files.
The law `two_pawn_four_wdl_is_fully_correct` connects those serialized bytes to
perfect-play strategies in both directions, alongside move soundness,
completeness, successor safety, and exact file-length proofs.

Stored roots have halfmove clock zero **and no en passant right**. These are
separate restrictions: a double push resets the clock to zero, too. En passant
is fully included during calculation after subsequent double pushes, but an
initial position with an en passant right cannot be looked up in these files.
The two-pawn implementation remains a slow reference definition, not an
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

Each file has 1,048,576 entries, one signed byte per encoded position:

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
