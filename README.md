# Bendbase

Chess WDL tablebases in Bend 2. Queries start at halfmove clock zero.
Castling is unavailable throughout play. Captures and pawn moves reset the
clock; other moves consume one halfmove. At 100 halfmoves, an existing terminal
result—including checkmate—takes precedence; otherwise the position is drawn.
Repetition history and optional draw claims are outside the model.

## Implementations

| Implementation | Scope | Correctness status |
| --- | --- | --- |
| Direct common generator: [chess_tables.bend](src/chess_tables.bend) | Arbitrary finite material, including pawns, promotions and en passant | Unconditional byte/strategy theorem; very expensive generation |
| Specialized clock-layer generators: [main.bend](main.bend), [four_main.bend](four_main.bend) | Pawnless three-man, KPK, and pawnless four-man | End-to-end WDL proofs for their existing formats |
| Specialized pawnful four-man definitions: [one_pawn_tables.bend](src/one_pawn_tables.bend), [two_pawn_tables.bend](src/two_pawn_tables.bend) | One pawn plus Q/R/B/N; KPPK and KPKP | Proved byte lists using game evaluation, not optimized clock-layer generation |
| Experimental common cached solver: [chess_solver.bend](src/chess_solver.bend) | Arbitrary ordered material signatures | Local compilation/solver proofs; full chess equivalence and successful generation remain unproved |

These implementations are not interchangeable: their indexes and file formats
differ. All support both color reversals and either side to move within their
respective material domains. No Syzygy-speed or Syzygy-format compatibility is
claimed. The direct common generator's bounded three-man benchmark did not
complete a table before reaching its memory guard.

## Check the proofs

With Bend installed, the repository manages Clang through mise:

```sh
mise install
mise exec -- bend PROOF.bend
```

The proof is structural: it does not enumerate chess positions or generate
tables. The project target is a proof check under three seconds.

[LAWS.bend](LAWS.bend) contains the public chess rules and end-to-end WDL
guarantees. Supporting statements are grouped into [chess laws](src/chess_laws.bend),
[cache laws](src/cache_laws.bend), and [legacy laws](src/legacy_laws.bend).
[PROOF.bend](PROOF.bend) imports and proves all four modules.

`Game.Forces` describes a player's forcing strategies independently of table
generation. `Game.CorrectByte` connects stored bytes to those strategies in
both directions for both players. Theorems certify the pure byte lists passed
to file writing, not pre-existing files. Bend's checker/compiler/runtime and
operating-system file IO are trusted execution boundaries. Specialized
correctness theorems retain their explicit valid-position and format premises.

## Direct common generator

[chess.bend](src/chess.bend) defines common move rules over two kings and an
arbitrary piece list: occupancy, slider obstruction, king safety, pawn pushes,
all four promotions, and en passant. Move enumeration is proved complete and
sound against those rules. Castling is never available.

[chess_game.bend](src/chess_game.bend) unfolds legal play into a finite game.
The termination measure combines piece count, summed pawn distance to promotion,
and remaining clock. Captures and pawn moves strictly decrease the reset
measure; quiet moves consume clock. The `NoCutoff` proof establishes that no
branch uses the artificial fuel cutoff, so the bound does not invent draws.

The actual generator directly tabulates this game's value. The public
`common_generated_wdl_is_fully_correct` law certifies its bytes without assumed
cache correctness or successful-compilation premises. Directory coverage,
exact-key lookup, serialization and file length also have structural proofs.
These results do not establish equivalence of the experimental cached solver.

The opt-in APIs are:

- `chess_tables.generate(capacity, 100n)`: a directory of every ordered material
  signature with up to `capacity` **non-king** pieces.
- `chess_tables.file(name, 100n)`: the byte list for one material signature.
- `chess_table_file.write(path, name)`: write that list to its own file.

The existing generation mains do not call these APIs. Direct game evaluation
repeats work across positions and move sequences, and the dense index consumes
substantial memory. Formal support for arbitrary material is not a claim of
practical scalability.

### Benchmark entrypoint

[benchmarks/bench_three_main.bend](benchmarks/bench_three_main.bend) invokes the
direct common generator for one three-man material. Build it without running
generation:

```sh
mkdir -p build
mise exec -- bend benchmarks/bench_three_main.bend -o build/bench-three
```

Its arguments are `-- <q|r|b|n|p> <output.wdl>`. Use a fresh output path and
external time **and memory** limits; interrupted output is not a usable table.
This entrypoint is separate from the specialized three-man generator.

## Specialized generators

Both use [clock_solver.bend](src/clock_solver.bend): terminal initialization
followed by 100 reversible-clock layers. Quiet moves read the preceding layer;
captures and pawn moves read completed dependencies at a fresh clock. KPK solves
pawn ranks nearest promotion first. The shared fill and byte-conversion code
uses balanced parallel table halves.

These generators retain domain-specific move rules, indexes and dependency
routing, with proofs connecting their serialized results to their chess games.
Representation bridges do not assume equivalence of independently defined
legal-move predicates.

### Three-man files

```sh
mkdir -p build
mise exec -- bend main.bend -o build/bendbase
./build/bendbase
```

This writes `kqk.wdl`, `krk.wdl`, `kbk.wdl`, `knk.wdl`, and `kpk.wdl` in
`build/`. Existing files are overwritten. The common-generator benchmark is
not a benchmark of this specialized implementation.

### Pawnless four-man files

Full four-man generation is opt-in; proof checking never runs it.

```sh
mkdir -p build
mise exec -- bend four_main.bend -o build/bendbase-four
./build/bendbase-four -- --help

# KQRK: both extras belong to the same player.
./build/bendbase-four -- q r same build/kqrk.wdl

# KQKR: extras belong to opposing players.
./build/bendbase-four -- q r opposed build/kqkr.wdl

# All 20 canonical pawnless material configurations.
./build/bendbase-four -- --all build
```

Kinds are `q/r/b/n`; either order is accepted for a single table. Keep that
order when encoding positions. Batch generation uses Q, R, B, N order and
shares three-man capture dependencies. Existing files are overwritten.
The first `--` separates Bend runtime options from generator arguments.
No practical four-man generation-time or memory guarantee is established.

## File formats

All formats use one byte per index slot:

| Byte | Meaning |
| --- | --- |
| `1` | White can force a win |
| `0` | Draw under perfect play |
| `255` (`-1` signed) | Black can force a win |

Squares are `a1 = 0` through `h8 = 63`; owner and turn are 0 for White and
1 for Black. The binary key value is the byte offset. These are custom files,
not Syzygy-compatible files. Invalid placements occupy slots; apply the
appropriate domain's validity predicate before interpreting a chess result.
Files do not encode arbitrary nonzero halfmove clocks or repetition history.

**Specialized three-man:** a 20-bit index, 1 MiB per file. From most to least
significant: owner, turn, piece square, black king, white king.

```text
offset = white_king + 64 * black_king + 4096 * piece
       + 262144 * turn + 524288 * owner
```

KPK uses the pawn square as `piece`; unpromoted pawns on ranks 1 and 8 are
invalid. EP cannot occur with only one pawn.

**Specialized four-man:** a 26-bit index, 64 MiB per file. The second piece's
square occupies the high six bits, above the three-man layout:
`offset = second_square * 1048576 + three_man_offset`.
One-pawn profiles put the pawn in the first slot and specify the other piece's
kind and relative owner. Two-pawn profiles distinguish KPPK from KPKP.
Stored roots have **no EP rights**, separately from the clock-zero requirement;
two-pawn continuations still include EP after double pushes.

**Direct common:** `21 + 6n` bits for `n` non-king pieces, with ordered square
slots followed by EP-enabled, owner, turn, EP target, black king and white king.
These files include EP states. A three-man file therefore has 27 bits and
128 MiB of final bytes, unlike a specialized three-man file.
See [position_index.bend](src/position_index.bend) for the exact encoding.

## Experimental cached solver

The general cached pipeline compiles [chess_graph.bend](src/chess_graph.bend)
into clock-solver components. Components use ordered material signatures and
the chess progress measure. Reset addresses read earlier stages; quiet
addresses stay within the same component. Missing dependencies and mismatched
widths cause explicit failure, not a draw.

Directory coverage, legal reset ordering, quiet closure, node compilation,
exact-key lookup and clock-layer updates have supporting proofs. The global
cache invariant theorem is conditional on `StageRule` at a fixed clock limit
and successful generation. Discharging those conditions against chess semantics
is still required before this pipeline can replace the proved direct generator.
Off-stage entries are padding, not assertions of drawn chess positions.
