# Pawnless WDL correctness

`mise exec -- bend PROOF.bend` checks the complete public theorem
`Laws.generated_wdl_is_fully_correct`, plus move coverage, index round-trip,
and file length. There are no open proof holes or unsafe definitions in the
active implementation or proof.

## Claim

For every valid placement of two kings and one queen, rook, bishop, or knight,
of either color, and either side to move, the byte at that position's encoded
offset in `Tables.file(100n, 20n, material)` has its exact perfect-play WDL
meaning from halfmove clock zero. A white-winning byte is equivalent to the
existence of a White forcing strategy; a black-winning byte is equivalent to
the existence of a Black forcing strategy; a draw permits neither.

The claim assumes no castling rights and the requested terminal-draw convention
at 100 halfmoves, with checkmate taking precedence. Stalemate and insufficient
material draw. With no pawns, the only clock reset is a capture; it leaves
K vs K and ends the relevant game immediately. Therefore 100 plies cover the
entire continuing game. Repetition history and optional-claim mechanics are
outside this model.

## Specification

`src/geometry.bend` states ordinary king, queen, rook, bishop, and knight
movement and obstruction. `src/pawnless_chess.bend` adds occupancy, king safety,
captures, material, turns, and terminal rules. Squares are six-bit values, so
the move domain consists of a king/piece choice and a destination square.

`Chess.forest` is the finite game tree specified by those rules and the clock.
It contains every legal continuation. At a zero remaining clock it still
recognizes already-delivered checkmate. It does not call the table generator,
read table values, or evaluate minimax.

`Game.Forces` independently describes a strategy on that tree: a choice on
the player's turn and a response to both branches on the opponent's turn.
Nonempty lists of legal moves become binary choices by the same player.
Terminal trees have explicit White-win, Black-win, or draw outcomes.

## Proof

1. `pawnless_moves_proof.bend` proves that the enumerated successors contain
   every legal action and contain only legal successors. Its induction ranges
   over symbolic finite trees, not board positions.
2. `game_proof.bend` proves minimax sound and complete for either player on
   every finite game tree. This proof has no chess or material parameters.
3. `pawnless_tables_proof.bend` proves the clock-layer generator agrees with
   evaluation of the rule-defined game tree. It inducts over the remaining
   clock and an arbitrary symbolic list of states. The material stays symbolic.
4. `pawnless_index_proof.bend` proves board encoding/decoding round-trips.
   `finite_table_proof.bend` proves canonical key coverage and that flattening
   a table puts each entry at its specified byte offset, with the exact length.
5. `PROOF.bend` combines those results into the public byte/strategy equivalence.

The root laws bind the constants 100 and 20 through equality premises. These
keep Bend's checker from normalizing a concrete game horizon or a million-entry
index tree. They impose no extra assumption on a position or generated table:
the writer uses those exact constants. All substantive induction remains over
symbolic inputs.

The active proof comprises roughly 850 lines across its helper modules, plus
the short root proof. Most of the finite-game proof is case analysis over the
three WDL outcomes. It does not generate tables or enumerate positions while
checking.

## Execution boundary

`src/table_file.bend` passes exactly the certified pure byte list to Bend's
`File.write_bytes` and propagates write errors. As usual, executing the theorem's
program trusts Bend's checker/compiler/runtime and the operating system's file
IO. This is not a proof of disk hardware or of pre-existing `.wdl` files.

The generator builds successfully with the repository-managed Clang. The new
four-table generation has not been run or benchmarked in this revision. The
uncertified table files from the earlier implementation have been removed.
