# 4×4 Othello: a forced win for White

[English](README.md) | [日本語](README-ja.md)

From the standard initial position, with Black moving first, White can force a win against every legal Black response.
The winner is determined by the final stone counts.

```text
    a b c d
 1  . . . .
 2  . W B .
 3  . B W .
 4  . . . .
```

B is Black, W is White, and a dot is an empty square.
[solutions/Othello4x4.v](../solutions/Othello4x4.v) states the initial board, problem and solution together.

## Proof and files

The Python program [generate_certificate.py](../generate_certificate.py) searches for a winning White strategy and writes it to `4x4/Certificate.v`.
At each White turn, the *certificate* records one chosen move; at each Black turn, it covers every legal reply. It also records forced passes and game end.
The checker in `Bounds.v` computes the resulting boards and verifies that White has more stones at every final board in the strategy.
Its soundness theorem proves that an accepted certificate gives White a winning strategy under the stated rules.

| File | Contents |
|---|---|
| [Rules.v](Rules.v) | Board, legal moves, flips, passes, game end and stone counts |
| [Bounds.v](Bounds.v) | White strategies, the certificate checker and its soundness proof |
| [Certificate.v](Certificate.v) | The generated strategy certificate |
| [CertificateResult.v](CertificateResult.v) | The successful certificate check and the White-win theorem |
| [RulesExamples.v](RulesExamples.v) | Examples covering edges, flips, passes, final boards and invalid certificates |
| [Certificate.json](Certificate.json) | Certificate statistics |

The soundness theorem is:

```coq
Theorem check_sound : forall fuel b p c,
  check fuel b p c = true -> white_wins b p.
```

There are 4 stones initially, so there are at most 12 placements. `fuel` bounds the depth of the check; it also counts passes and the final-board check.
The certificate's longest path has 15 nodes including that check. With repeated subtrees shared, it has 197 nodes; as a tree, it has 589.

[proofs/equivalence/Four.v](../proofs/equivalence/Four.v) proves agreement with the [common rules](../common/README.md).
[proofs/certificates/Four.v](../proofs/certificates/Four.v) derives the result in those common definitions.

## Build and check

Use Rocq 9.2 / OCaml 5.3.0, Python 3.11 or later, and GNU make. From the project root:

```text
make check-4x4
```

This builds the rules, certificate, common definitions and 4×4 result from source, then runs an independent kernel check.
The sources in Git are sufficient. By default, build output goes to `_build/`.
The soundness, certificate-check and White-win theorems have no added axioms.
See the [build instructions](../README.md#checking) for options.

To regenerate the small certificate:

```text
make certificate-4x4
make check-4x4
```

The generator writes `4x4/Certificate.v` and `4x4/Certificate.json`.
It visits Black's moves in square-number order and chooses White's first move that guarantees a win. The same source produces the same certificate.
