# 証明の読み方

[English](README.md) | [日本語](README-ja.md)

まず [4×4](../solutions/Othello4x4.v)・[6×6](../solutions/Othello6x6.v) の問題文と証明を読んでください．

| 段階 | 4×4 | 6×6 |
|---|---|---|
| 共通定義に盤面サイズと型を渡す | [boards/Four.v](../boards/Four.v) | [boards/Six.v](../boards/Six.v) |
| 証明書側の定義との一致を証明する | [equivalence/Four.v](equivalence/Four.v) | [equivalence/Six.v](equivalence/Six.v) |
| 検査した結果を共通定義で表す | [certificates/Four.v](certificates/Four.v) | [certificates/Six.v](certificates/Six.v) |

合法な着手，合法手一覧，パスの条件，終局，石数，戦略の対応を，任意の盤面について証明しています．
[common/proofs/](../common/proofs/) には，ルール，戦略，ゲームの値についての一般的な定理を置いています．

6×6の[値の一意性](../6x6/Semantics/Optimal.v)には共通の定理を使います．
[最善手による対局の補題](../6x6/Semantics/OptimalReplay.v)にも，共通の定義と，その定義が意図した結果を表すことの証明を使います．
このため，二つの戦略を対戦させられることの証明は，共通部分だけに置いています．

証明書との接続には，具体的なルールの補題，`Bounds.v` の戦略，`6x6/Replay.v` の対局を再現する操作を使います．
証明書の実装側はそれぞれの型とインターフェースを使い，問題文は共通理論の定義を使っています．
検査を速くするための別の盤面表現については，[6x6/README-ja.md](../6x6/README-ja.md)で説明しています．

4×4では，[Bounds.v](../4x4/Bounds.v) の `check_sound` を [CertificateResult.v](../4x4/CertificateResult.v) で生成済みの証明書に適用します．
6×6では，必須の[別添証明書ソース](../distribution/README-ja.md)で証明した石数差−4の上下限を，[CertificateResult.v](../6x6/CertificateResult.v) で組み合わせます．
[OptimalPlay.v](../6x6/OptimalPlay.v) は，記録された一つの対局の全33局面についてゲームの値を証明します．

ビット盤面の石数を共通定義へ移す際は，`count_agrees` で先に数える関数を書き換えてから，具体的な石数の定理を適用します．
これにより，型の照合中に大きな整数を展開することを避けています．
`solutions/` の各ファイルには，初期盤面と定理の言明をまとめて明示しています．

## 追加の検査

[Audit6.v](Audit6.v) は，6×6の主要な定理と，それらが依存するすべての定理について公理への依存を調べます．
全体をカーネルで再検査するコマンドも用意しています．

```text
make audit-6x6
make kernel-6x6
```

これらの追加検査は `make check-6x6` には含まれません．
対象範囲と実施状況は [6x6/README-ja.md](../6x6/README-ja.md) を参照してください．
