# Following the proofs

[English](README.md) | [日本語](README-ja.md)

Start with the problems and proofs for [4×4](../solutions/Othello4x4.v) and [6×6](../solutions/Othello6x6.v).

| Step | 4×4 | 6×6 |
|---|---|---|
| Instantiate the common definitions | [boards/Four.v](../boards/Four.v) | [boards/Six.v](../boards/Six.v) |
| Prove agreement with the certificate definitions | [equivalence/Four.v](equivalence/Four.v) | [equivalence/Six.v](equivalence/Six.v) |
| Express the checked results with the common definitions | [certificates/Four.v](certificates/Four.v) | [certificates/Six.v](certificates/Six.v) |

The equivalence proofs cover legal placements, move lists, pass conditions, game end, stone counts and strategies.
They apply to arbitrary boards.
The files in [common/proofs/](../common/proofs/) prove the general facts about rules, strategies and game values.

The 6×6 [score theorem](../6x6/Semantics/Optimal.v) uses the common uniqueness theorem.
The [best-play lemmas](../6x6/Semantics/OptimalReplay.v) use the common definition and its soundness theorem.
The proof that two strategies can be played against each other is therefore needed only in the common theory.

The certificate interfaces include concrete rule lemmas, the strategies in `Bounds.v`, and the game replay operations in `6x6/Replay.v`.
These retain the certificate implementation's own types and interfaces. The common theory supplies the definitions used in the problem statements.
The separate board representations used to speed up checking are described in [6x6/README.md](../6x6/README.md).

For 4×4, [Bounds.v](../4x4/Bounds.v) proves `check_sound`, and [CertificateResult.v](../4x4/CertificateResult.v) applies it to the generated certificate.
For 6×6, [CertificateResult.v](../6x6/CertificateResult.v) combines the lower and upper bounds of −4 proved by the required [separate certificate sources](../distribution/README.md).
[OptimalPlay.v](../6x6/OptimalPlay.v) proves the game value at all 33 positions of one recorded game.

When transferring bitboard stone counts, `count_agrees` rewrites the counting function before applying the concrete count theorem.
This avoids expanding large integers during type conversion.
Each file in `solutions/` displays the initial board and theorem statements together.

## Additional checks

[Audit6.v](Audit6.v) audits the assumptions of the main 6×6 theorems and all their dependencies.
The full kernel recheck is a separate command.

```text
make audit-6x6
make kernel-6x6
```

These additional checks are not part of `make check-6x6`.
See [6x6/README.md](../6x6/README.md) for their scope and recorded status.
