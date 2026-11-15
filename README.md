# TPP-mark 2026: 4×4 and 6×6 Othello

[English](README.md) | [日本語](README-ja.md)

## How this work was created

These are Rocq solutions to the 4×4 and 6×6 Othello problems in [TPP-mark 2026](https://auto-res.github.io/tpp2026/ja/tpp2026mark/).
We used Codex to write and revise the code, proofs, certificate generators and documentation.

We searched for strategies with programs run outside Rocq: the included Python program [generate_certificate.py](generate_certificate.py) for 4×4, and C programs written for this project for 6×6.
These programs record chosen moves and the opponent's possible replies. We call these data *strategy certificates*.

Rocq checks the certificates against the game rules and the required final scores.
The proofs use these checks and a proof that the checker accepts only valid strategies.
See the [6×6 certificate explanation](6x6/README.md#certificate-data) for the programs used during development and the data needed to check the result.

## Results

The problem statements and proofs are in **[4×4](solutions/Othello4x4.v)** and **[6×6](solutions/Othello6x6.v)**.
See the [common rule guide](common/README.md) for the rules used by both sizes.
Each solution file puts the initial board, `problem` definition and `solution` theorem together.

| Board | Result |
|---|---|
| 4×4 | White can force a win against every legal Black strategy |
| 6×6 | With best play on both sides, the final score (black stones minus white stones) is −4 |
| 6×6 example | All 32 moves are best moves; the final board has 16 black stones and 20 white stones |

For 6×6, `solution` proves that Black can guarantee at least −4 and White can guarantee at most −4.
`optimal_line` proves that the displayed game consists of best moves and ends with 16 black stones and 20 white stones.
The general theorem covers complete finite games in which every legal move or forced pass preserves the game value; it proves a final score of −4.
The individual counts of 16 and 20 are proved for the displayed game.

## Source distribution

This package contains source files only. It includes no `.vo` files or compiled plugins.
The small source files are in Git. The large generated 6×6 certificate sources are packaged in **5 separate `.tar.gz` files, totalling about 2.92 GB**.
See the [file list and download instructions](distribution/README.md#certificate-archives).

**The separate certificate sources are required to build and check the 6×6 proof. The files in Git alone are not sufficient.**
The archives contain strategy data and proofs used by the main theorem. These sources are part of the proof.
The complete 4×4 proof is included in Git.

| Directory | Contents |
|---|---|
| `common/` | Shared rules, strategy definitions and supporting lemmas |
| `boards/` | Instances of the common definitions for each size |
| `solutions/` | Initial positions, problem statements and main theorems |
| `4x4/`, `6x6/` | Rules used by the certificate checkers, the checkers themselves and solution proofs |
| `proofs/equivalence/` | Proofs that the certificate rules agree with the common definitions |
| `proofs/certificates/` | The checked certificate results in the common definitions |
| `distribution/` | File inventories, hashes, documentation checks and build records |

Both sizes use `Rules.v`, `Bounds.v`, `CertificateResult.v` and `RulesExamples.v` for the same roles.
The small 4×4 certificate is `4x4/Certificate.v`; the 6×6 certificates are split across many files.
The separate proof of best play is `6x6/OptimalPlay.v`.
`solutions/` states and proves the results using the common definitions; `4x4/CertificateResult.v` and `6x6/CertificateResult.v` establish the results using the certificate definitions.
The directories `4x4/` and `6x6/` map to the Rocq namespaces `TPP2026.Four` and `TPP2026.Six` in `_CoqProject` and the build script.

<a id="checking"></a>

## Build and check

Use Rocq 9.2 / OCaml 5.3.0, Python 3.11 or later, and GNU make.
The scripts use Unix file locks and filesystem hard links.
Put `rocq` on PATH, or add `ROCQ=/absolute/path/to/rocq` to a command.
For 6×6, use `ocamlfind` and `ocamlopt` from the same toolchain as Rocq.
By default, the build looks for `ocamlfind` beside the Rocq executable. Use `OCAMLFIND=/absolute/path/to/ocamlfind` to set another location.
Run commands from the repository root.

The complete 4×4 result needs only the sources in Git:

```text
make check-4x4
```

**Allow several hours for the first 6×6 build and proof check.**
A clean build of both sizes from an earlier source revision took about **5 hours 26 minutes** with Rocq 9.2 / OCaml 5.3.0 and `JOBS=8 LINK_JOBS=1 INTERFACE_JOBS=4`.
Most of that time was spent on 6×6. The time depends on the machine and settings.
This measurement does not include the additional full 6×6 assumption audit or independent kernel check.

**For a fresh 6×6 build, the build script requires at least 70 GB of free disk space after the sources have been unpacked.**

To check 6×6, obtain all 5 certificate archives using the [download instructions](distribution/README.md#certificate-archives).
Replace `/path/to/archives` with the directory holding the downloaded files and run:

```text
make unpack-certificates ARCHIVE_DIR=/path/to/archives
make check-disk
make check-certificate-files
make check-6x6
```

The unpack command checks every archive before writing sources, then checks each extracted file against the inventory. It stops if a certificate directory already exists; if the sources are already in place, skip that command.
Use `make check` to check both sizes. `make check-disk` checks free space, and `make check-certificate-files` checks source sizes and hashes. These preparation commands do not check proofs.

The build can resume or add 6×6 after checking 4×4 in the same directory.
To require a new or empty build directory, add `FRESH=1` to the build command.
The build compiles the plugins, checks each part of the certificate, proves that those parts form a complete strategy, and compiles the main theorems.
When checking 4×4, it also runs an independent kernel check of that result.
By default, build output and records go under `_build/`, outside the source distribution.

| Command | Scope |
|---|---|
| `make check-4x4` | Build the 4×4 definitions and proofs, then recheck them with the kernel |
| `make check-6x6` | Build the 6×6 definitions and proofs, including all certificate blocks |
| `make check` | Run both builds |
| `make audit-6x6` | Build 6×6 and audit all dependencies of its main theorems |
| `make kernel-6x6` | Build 6×6 and independently check the full result with the kernel |
| `make check-archives ARCHIVE_DIR=/path/to/archives` | Check archive sizes and SHA-256 hashes without unpacking |
| `make unpack-certificates ARCHIVE_DIR=/path/to/archives` | Check all archives, then unpack and check the certificate sources |
| `make review-files` | Check the source inventory and the English/Japanese README pairs |

<a id="disk-use"></a>

## Disk use and build options

The following measurements come from a build of an earlier source revision. They include both board sizes. Sizes are sums of file lengths; 1 GB means 1,000,000,000 bytes.

| Files | Measured size |
|---|---:|
| Unpacked 6×6 certificate sources | 8.92 GB |
| Files added by the build, including objects, plugins, logs and build records | 32.24 GB |
| Sources and build files together, counting hard links once | About 41.2 GB |

The `.vo` files alone account for 32.21 GB. They are generated during the build even though they are not distributed.
The large certificate sources are hard-linked into the build directory, so they do not take another 8.92 GB there.
Keep the 6×6 certificate sources and build directory on the same filesystem; the build stops if it cannot make those links.

**For a fresh 6×6 build, keep at least 70 GB free after unpacking the sources.**
The preflight check allows 50 GB for build output and a further 20 GB of headroom.
Before unpacking, allow about 80 GB for the extracted sources and this build allowance, plus about 2.92 GB for the downloaded archives.
The Rocq/OCaml installation and any operating-system swap use are not included in these figures.
Actual disk allocation depends on the filesystem. Temporary peak use was not measured; 70 GB is the preflight allowance, not a measured peak.
For a resumed build, the check subtracts existing objects when estimating the additional space needed.

Use `BUILD_DIR=/path/to/build` to choose the output directory.
If the certificate sources already exist elsewhere, use `CERTIFICATE_SOURCE=/path/to/sources`. This directory must contain `6x6/InitialLower/` and the other certificate directories listed in the distribution guide. The build reads only the listed sources, never compiled objects from that location.
`JOBS=4`, `LINK_JOBS=1` and `INTERFACE_JOBS=4` are the defaults for parallel certificate blocks, link batches, and data/interface modules, respectively.
The 6×6 build can use tens of GB of memory.
`MODULE_TIMEOUT=1800` is the time limit in seconds for each ordinary Rocq compilation and the 4×4 kernel recheck; 0 disables the limit.
The full 6×6 assumption audit, full 6×6 kernel recheck and parallel link batches have no such limit.

See [4x4/README.md](4x4/README.md), [6x6/README.md](6x6/README.md) and [proofs/README.md](proofs/README.md) for the proof structure.
[distribution/verification.json](distribution/verification.json) records the scope and outcome of the checks.
