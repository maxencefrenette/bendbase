# Bendbase

A three-man chess endgame WDL tablebase generator written in Bend 2. It builds
KQK, KRK, KBK, KNK, and KPK with the extra piece on White's side. A position
with the extra piece on Black's side is equivalent after swapping colors and
flipping ranks (`square ^ 56`). K vs K is always drawn.

## Build and generate

Install [Bend 2](https://github.com/bendlang/bend#1-install) and
[mise](https://mise.jdx.dev/getting-started/). This repo pins Clang 21.1.8 with
mise. On Linux:

```sh
mise install
bend version
mise exec -- clang --version
mise exec -- bend main.bend --check-only
mise exec -- bend PROOF.bend
mkdir -p build
mise exec -- bend main.bend -o build/bendbase
./build/bendbase
```

The proof-first generator builds 100 clock layers for each non-pawn class and
seven pawn-push budget layers. KBK and KNK are direct all-zero
insufficient-material draws. It writes one file per material class. The
previous queue-based generator and its exhaustive verifier remain in `src/`
and `verify.bend` for comparison; they do not certify the new entry point.
The formal proof is still incomplete; see [CORRECTNESS.md](CORRECTNESS.md).

## Format

Each `.wdl` file contains exactly 524,288 bytes. Square numbers are `a1 = 0`
through `h8 = 63`. Look up one byte at:

```text
index = white_king + 64 * black_king + 4096 * extra_piece + 262144 * turn
turn  = 0 for White, 1 for Black
```

A byte of `1` means the extra-piece side can force a win from halfmove clock
zero before the 100-halfmove draw boundary. At that boundary the defender is
assumed to claim a draw, unless the move itself ended the game by checkmate.
Zero means draw
for a legal position; it also marks invalid positions, so callers must apply
`Rules.valid` before a lookup. Black-extra-piece positions must first be
normalized by swapping the kings, flipping every occupied square vertically
(`square ^ 56`), and swapping the side to move. Pawns then always advance
toward increasing square numbers.

The files do not encode arbitrary nonzero halfmove clocks; the generator
computes those clock layers internally and stores only clock-zero results.
Castling rights are excluded. En passant is impossible with only one pawn. A
promotion considers queen, rook, bishop, and knight; capturing the extra piece
leads to the drawn K vs K ending.

See [CORRECTNESS.md](CORRECTNESS.md) for the proof status. `PROOF.bend` proves
the clocked tree construction agrees with independent direct minimax
recursions, by symbolic induction rather than a scan of table entries. The
remaining bridge to the quantified perfect-play game semantics is open. The
generator uses no external chess library or foreign solver.
The current `bend PROOF.bend` check takes about 15 seconds here, above the
five-second project target.
