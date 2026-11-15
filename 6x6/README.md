# 6×6 Othello: optimal score −4

[English](README.md) | [日本語](README-ja.md)

From the standard initial position, with Black moving first, the optimal final score is −4, counting black stones minus white stones.
Black can guarantee at least −4 against any White play, and White can guarantee at most −4 against any Black play. We call this optimal score the *game value*.

[solutions/Othello6x6.v](../solutions/Othello6x6.v) contains the initial position and solution.
`optimal_line` proves that all 32 moves of one recorded game are best moves, ending with 16 black stones and 20 white stones.
`value_unique` proves uniqueness of the game value.
`every_optimal_line_has_score_minus_four` proves a final score of −4 for every complete finite game satisfying `optimal_replay`: each move or forced pass is legal and preserves the game value.
The individual counts of 16 and 20 are proved for the displayed game. The general theorem gives the difference between the counts.

**Building and checking the 6×6 main theorem requires both the Git sources and the separate certificate sources.**
The 5 archives contain the concrete Black and White strategy data, together with the proofs that check and combine it.
These files are part of the proof; the sources in Git alone cannot build or check the main theorem.

<a id="certificate-data"></a>

## How the certificate data was made

During development, we used the C programs `search6_v2.c` and `export_strategy6_v2.c` to search for and record strategies outside Rocq.
Python tools, including `make_block_proof.py`, converted the recorded data into Rocq source files.
These search and conversion tools and their intermediate databases are not included in this distribution.
To rebuild and check the proofs, use the generated Rocq sources in the separate certificate archives; the build does not repeat the original search.

A *strategy certificate* records a chosen move on the player's turn and covers every legal reply on the opponent's turn.
Repeated positions share data in a directed acyclic graph (DAG).
The certificates are split into smaller parts, called *blocks*, so that Rocq can check them separately.
When a block refers to a result from another block, a linking proof supplies that result and proves that the parts form a complete finite strategy.

## Proof and files

The checkers compute the boards after chosen moves and every legal opposing reply, and check forced passes and final scores.
White's upper bound is checked after Black plays c2 and extended by symmetry to all 4 legal first moves. Here columns run from a to f, left to right, and rows from 1 to 6, top to bottom.

| Part | Files |
|---|---|
| Rules and strategies | [Rules.v](Rules.v), [Bounds.v](Bounds.v), [Replay.v](Replay.v), [Semantics/](Semantics/) |
| Score and best-play results | [CertificateResult.v](CertificateResult.v), [OptimalPlay.v](OptimalPlay.v) |
| Rule examples | [RulesExamples.v](RulesExamples.v) |
| Symmetries used in the proof | [Symmetry.v](Symmetry.v), [InitialSymmetry.v](InitialSymmetry.v) |
| DAG and block checkers | [Dag.v](Dag.v), [BlockDag.v](BlockDag.v), [CutDag.v](CutDag.v) |
| Fast board operations | [GridExp/](GridExp/) |
| Positions and results passed between blocks | [ExportExp/](ExportExp/) |
| Certificate linking | [LinkExp/](LinkExp/) |
| Agreement with common definitions | [proofs/equivalence/Six.v](../proofs/equivalence/Six.v), [proofs/certificates/Six.v](../proofs/certificates/Six.v) |

[OptimalPlay.v](OptimalPlay.v) proves the optimal score at all 33 positions of the given game.
The checkers' soundness and the agreement of their fast board representation with the rules are proved in Rocq.

The list-based rules are the reference for the certificate checkers; see the [common rule guide](../common/README.md) for their relation to the shared definitions.
A bitboard represents occupied squares by bits in an integer. Cached rays store the sequences of squares in each direction, computed in advance.
These speed up repeated board operations; their agreement with the list-based rules is proved in Rocq.
Compression reduces the size of the stored data, while block linking lets us combine separately checked results.

The source archives contain these certificates and their linking proofs:

| Certificate | Strategy DAG nodes | Blocks | Directories |
|---|---:|---:|---|
| Black's lower bound of −4 | 43,160,560 | 1,439 | `InitialLower/`, `InitialLowerCompact/` |
| White's upper bound of −4 after c2 | 118,749,546 | 1,320 | `InitialUpper/`, `InitialUpperLocalCompact/` |

In the upper-bound certificate, short endgames are repeated within blocks to reduce references between blocks. The checker therefore processes 146,623,347 data entries, more than the number of shared DAG nodes.
See the [certificate inventory](../distribution/certificates.tsv) and [distribution guide](../distribution/README.md).

## Build from source

Use Rocq 9.2 / OCaml 5.3.0, Python 3.11 or later, GNU make, and the matching `ocamlfind` and `ocamlopt`.

**Allow several hours for the first build and proof check of this 6×6 solution.**
The [root build instructions](../README.md#checking) give the measured time and settings for our clean build.

**For a fresh 6×6 build, the build script requires at least 70 GB of free disk space after the sources have been unpacked.**

Obtain all 5 certificate archives and follow the [download and unpacking instructions](../distribution/README.md#certificate-archives).
Once the sources are in place, run these commands from the repository root:

```text
make check-disk
make check-certificate-files
make check-6x6
```

No precompiled project library is supplied or needed as input. The build compiles the base rules, OCaml plugins, certificate blocks, links, final results and solution stated with the common definitions.
It uses only project sources listed in the distribution inventories, plus the installed Rocq/OCaml toolchain.
It clears inherited settings for additional library search paths and does not load a user Rocq startup file.
By default, build output and cache records go to `_build/`.
The build can resume; successful modules are reused only after source and object checks.
Add `FRESH=1` to require a new or empty build directory.

The recorded build of both sizes added about 32.24 GB of files; sources and build files together occupied about 41.2 GB.
The 70 GB free-space requirement applies after unpacking: it allows 50 GB for build output and a 20 GB reserve.
Before unpacking, allow about 80 GB plus about 2.92 GB for the downloaded archives; the toolchain and OS swap use are separate.
Certificate sources are hard-linked into the build tree on the same filesystem, so the build does not make another 8.92 GB source copy.
See the [disk-use breakdown](../README.md#disk-use) for the measurements and what they include. Temporary peak use was not measured.
The build can use tens of GB of memory.
See the [root instructions](../README.md#checking) for `BUILD_DIR=/path/to/build`, `CERTIFICATE_SOURCE=/path/to/sources`, `ROCQ=/absolute/path/to/rocq` and parallelism options.

## Further checks and records

| Command | Scope |
|---|---|
| `make audit-6x6` | Audit assumptions of the main theorems and all dependencies after building |
| `make kernel-6x6` | Independently check the full result with the kernel after building |

The source-only build compiled the certificate blocks, their linking proofs and the main theorems. Normal compilation checks the resulting proof terms.
For the current sources, changed proofs and their dependent main theorems were compiled with previously checked certificate objects; formatting changes were checked by comparing Rocq token streams. A fresh build of the entire current 6×6 source tree has not been run.
The two commands above perform additional checks: the assumption audit checks whether the theorems depend on axioms, and the independent kernel check rechecks the saved compiled proofs.
They are not part of `make check-6x6`. Neither full 6×6 additional check has been run.
[verification.json](../distribution/verification.json) records the source-only rebuild and the checks that were run.
