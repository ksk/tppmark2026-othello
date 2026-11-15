# Certificate sources and verification

[English](README.md) | [日本語](README-ja.md)

The 4×4 proof can be built and checked from the files in Git alone.
**For 6×6, you also need all 5 certificate source archives listed below.**
They contain the strategy data and proofs used by the main theorem.
The package contains sources only; it includes no `.vo` files or compiled plugins.

<a id="certificate-archives"></a>

## Download the certificate sources

Open the repository's [Releases page](https://github.com/ksk/tppmark2026-othello/releases) and select the release matching your source checkout.
Download all 5 files below from its assets into one directory.
GitHub's automatic “Source code” downloads contain only the Git files, without these certificate archives.

| File | Bytes |
|---|---:|
| `tppmark2026-othello-6x6-certificates-01-of-05.tar.gz` | 586,962,086 |
| `tppmark2026-othello-6x6-certificates-02-of-05.tar.gz` | 550,625,706 |
| `tppmark2026-othello-6x6-certificates-03-of-05.tar.gz` | 600,701,274 |
| `tppmark2026-othello-6x6-certificates-04-of-05.tar.gz` | 608,348,504 |
| `tppmark2026-othello-6x6-certificates-05-of-05.tar.gz` | 568,892,691 |

The compressed files total **2,915,530,261 bytes (about 2.92 GB)**.
Each is an independent `.tar.gz` archive. All 5 are required; no concatenation is needed.
The [archive record](archives.json) gives their exact sizes and SHA-256 hashes.
The checking commands use this record and [certificates.tsv](certificates.tsv) from your checkout.
The copies of `archives.json`, `certificates.tsv` and [SHA256SUMS](SHA256SUMS) among the release assets are optional for these commands.

## Check and unpack

Use Python 3.11 or later and GNU make. Run commands from the repository root.
Replace `/path/to/archives` with the directory containing the downloaded files.
To check their sizes and SHA-256 hashes without unpacking them:

```text
make check-archives ARCHIVE_DIR=/path/to/archives
```

To check all archives, unpack them, and compare every extracted file with the inventory:

```text
make unpack-certificates ARCHIVE_DIR=/path/to/archives
```

The unpack command includes the archive check, so a separate check is optional.
No separate `tar` or checksum program is needed.
The command creates these 4 directories under `6x6/`:

| Directory | Contents |
|---|---|
| `6x6/InitialLower/`, `6x6/InitialUpper/` | `Goal.v`, `B*.v`, `Links.v`, `Result.v` and a build manifest |
| `6x6/InitialLowerCompact/`, `6x6/InitialUpperLocalCompact/` | `D*.v`, `E*.v`, `K*.v`, `Links.v` and a build manifest |

The inventory lists **8,376 files: 8,372 Rocq sources and 4 JSON build manifests**, totalling **8,924,569,050 bytes (about 8.92 GB)** after unpacking.
A build manifest lists the certificate blocks and their dependencies.
The provenance fields `source` and `meeting_line` can name files used during the original search. Those search databases and game JSON files are not build inputs.
Each linking manifest's `source` field points to a block directory included in the archives.

Unpacking stops if any of the 4 certificate directories already exists.
If the sources are already in place, skip unpacking and use `make check-certificate-files`.
To unpack elsewhere, add `CERTIFICATE_SOURCE=/path/to/sources`; use the same setting for the build and certificate-file checks.
This path must name the directory containing `6x6/InitialLower/` and the other certificate directories.

Unpacking writes about 8.92 GB of sources, without an intermediate uncompressed archive or a second source copy.
The unpacker requires the source size plus 1 GB of free space. This covers unpacking only; the build needs the larger allowance below.
After successful unpacking and checking, you can remove the downloaded archives to recover space. Keep all extracted certificate sources for the build.

## Build and check the proofs

**Allow several hours for the first 6×6 build and proof check.**
Use the toolchain and settings in the [root build instructions](../README.md#checking).
For a fresh 6×6 build, keep at least **70 GB free after unpacking**.
Before downloading and unpacking, allow about **80 GB plus 2.92 GB for the archives**, excluding the toolchain and operating-system swap.
See the [disk-use explanation](../README.md#disk-use) for measured sizes and the meaning of this allowance.

With the certificate sources in place, check both sizes with:

```text
make check-disk
make check-certificate-files
make check
```

Use `make check-6x6` for 6×6 alone.
The disk and file checks do not check proofs; the build compiles and checks the Rocq proofs.
By default, objects, plugins and logs go to `_build/`. Use `BUILD_DIR=/path/to/build` for another location.
The build directory must be on the same filesystem as the certificate sources: the build hard-links those sources instead of copying another 8.92 GB.
Use the same command to resume a build. Add `FRESH=1` to require a new or empty build directory.
See the [6×6 guide](../6x6/README.md) for the separate full assumption audit and independent kernel check.

## Inventories and validation records

| File | Contents |
|---|---|
| [git-files.txt](git-files.txt) | Source files included in the repository |
| [certificates.tsv](certificates.tsv) | Paths, sizes and SHA-256 hashes of the certificate sources |
| [archives.json](archives.json) | Archive sizes, SHA-256 hashes and file-integrity checks |
| [SHA256SUMS](SHA256SUMS) | Checksums for the release assets |
| [verification.json](verification.json) | Toolchain, proof-validation scope, build measurements and checks not run |

To check the repository file inventory and the English/Japanese README pairs:

```text
make review-files
```

This does not read the large certificate files or check proofs.
Use `make check-certificate-files` to check extracted sources and `make check-archives ARCHIVE_DIR=/path/to/archives` to check downloads.
The documentation check compares commands, identifiers, links and recorded file hashes. It cannot establish that translations have the same meaning.

Search databases, checkpoints, intermediate JSONL and the original 6×6 search and conversion programs are not included.
The build checks proofs from the supplied certificate sources; it does not regenerate those certificates by searching the game tree.
See the [6×6 certificate explanation](../6x6/README.md#certificate-data) for their origin.
