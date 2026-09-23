# Bendbase

A Bend 2 generator for pawnless three-man WDL tables: KQK, KRK, KBK, and KNK.
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
checker run takes about 0.3 seconds on this container. See
[CORRECTNESS.md](CORRECTNESS.md) for its scope and proof structure.

## Generate

The repository pins Clang through mise. With Bend installed:

```sh
mkdir -p build
mise exec -- bend main.bend -o build/bendbase
./build/bendbase
```

The generator builds 100 clock layers and writes four files in `build/`.
This implementation prioritizes the proof; the new four-table generation has
not yet been run or benchmarked. Obsolete tables from the earlier implementation
have been removed.

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
are `kqk.wdl`, `krk.wdl`, `kbk.wdl`, and `knk.wdl`. These are simple custom WDL
files, not Syzygy-compatible files. Invalid placements occupy zero-valued slots;
callers must apply `Chess.valid` before interpreting an entry as a chess result.

Checkmate takes precedence on the move reaching 100 halfmoves. Otherwise that
boundary is a terminal draw, following the agreed tablebase convention.
Stalemate, insufficient material, and captures leaving K vs K are draws.
The files do not store arbitrary nonzero halfmove clocks or repetition history.
