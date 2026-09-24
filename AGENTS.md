This codebase is in bend, which lets us prove correctness instead of using tests.

## When using Bend
- Run `bend guide` to learn it
- Use `LAWS.bend` to keep important rules
- Run `bend PROOF.bend` before committing
- Parallelize the code whenever possible

## Invariants and project goals
From most to least important:
- Correctness of the tablebase must be formalized and proven using bend
- `bend PROOF.bend` must run in under 3 seconds
- Generating tables must be at least as fast as syzygy
- Random reads on tables must be at least as fast as syzygy
- The generated tables must be as small as possible

## Scope
- WDL tables (no DTZ, DTM)
- Pawnless 3-man positions and KPK (either pawn color)
- All four-man material configurations: chess semantics and WDL correctness proofs
- Executable pawnless four-man clock-layer generator, proved directly against the chess semantics
- Pawn-containing four-man byte lists use the generic game evaluator; no optimized generator yet
- Four-man stored roots have no castling or en passant rights; en passant is included in continuations
- Do not run full four-man table generation unless explicitly requested
