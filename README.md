# Bendbase

A Bend 2 generator for three-man WDL tables: KQK, KRK, KBK, KNK, and KPK.
Each table includes either owner of the extra piece and either side to move.
Queries start at halfmove clock zero. Castling rights are excluded.

The complete correctness theorem is in [LAWS.bend](LAWS.bend). It connects
the bytes produced by the generator to perfect-play strategies under the
specified chess rules, in both directions for both players. Run:

```sh
mise install
mise exec -- bend PROOF.bend
```

The proof is structural and does not enumerate chess positions. The current
checker run takes about 0.5 seconds on this container. The comments in
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

This is a **proof-only milestone**: no four-man tables have been generated,
and `main.bend` still generates only the five three-man files. The reference
recurrence is not memoized and is not intended for practical table generation;
no generation-speed claim is made. A performant generator and four-man pawn
support remain later work. Existing three-man generators and proofs are intact.

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
