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
checker run takes about 0.4 seconds on this container. The comments in
[LAWS.bend](LAWS.bend) document the theorem's scope and execution boundary.

## Four-man groundwork

`src/material_chess.bend` provides material-independent pawnless positions and
move rules: two kings plus a list of colored pieces, with full-board obstruction,
captures, and king safety. `PROOF.bend` checks move-generation completeness and
soundness, successor validity, and lossless conversion from three-man boards.
The move domain is all 12-bit source/destination pairs; the proof keeps this
domain symbolic rather than checking individual positions.

This is the foundation for four-man generation, not a four-man tablebase yet.
The existing three-man generators and their proofs remain unchanged. They have
not migrated to this new move layer, and equivalence of the old and new legality
predicates is not yet proved. Four-man terminal evaluation, clock-aware solving,
indexing, serialization, and pawn support are subsequent milestones.

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
