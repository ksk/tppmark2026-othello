# 4×4 Othello：白必勝の証明

[English](README.md) | [日本語](README-ja.md)

標準初期局面から黒が先手で始めると，黒のどの合法な応手に対しても白は勝利を保証できます．
終局時の石数で勝敗を決めます．

```text
    a b c d
 1  . . . .
 2  . W B .
 3  . B W .
 4  . . . .
```

Bは黒，Wは白，点は空きマスです．
[solutions/Othello4x4.v](../solutions/Othello4x4.v) に初期盤面，問題文，証明をまとめています．

## 証明とファイル

Pythonプログラム [generate_certificate.py](../generate_certificate.py) が白の必勝戦略を探索し，`4x4/Certificate.v` に書き出します．
この「証明書」は，白の手番ごとに選ぶ1手を，黒の手番ごとに全合法手への応答を記録したデータです．強制パスと終局も扱います．
`Bounds.v` の検証器が着手後の盤面を計算し，戦略中のどの終局でも白の石数が多いことを確かめます．
健全性の定理は，検証器が受理した証明書から，定義したルールの下で白の必勝戦略が得られることを示します．

| ファイル | 内容 |
|---|---|
| [Rules.v](Rules.v) | 盤面，合法手，反転，パス，終局，石数 |
| [Bounds.v](Bounds.v) | 白の戦略，証明書検証器，健全性の証明 |
| [Certificate.v](Certificate.v) | 生成済みの戦略証明書 |
| [CertificateResult.v](CertificateResult.v) | 証明書の検査成功と白必勝の定理 |
| [RulesExamples.v](RulesExamples.v) | 盤端，反転，パス，終局，不正な証明書の検査例 |
| [Certificate.json](Certificate.json) | 証明書の統計 |

健全性の定理は次のとおりです．

```coq
Theorem check_sound : forall fuel b p c,
  check fuel b p c = true -> white_wins b p.
```

初期局面には4石あるため着手は高々12回です．`fuel` は検査でたどれる深さの上限で，パスと終局確認も数えます．
この証明書の最長経路は終局確認を含めて15ノードです．重複する部分を共有すると197ノード，木として展開すると589ノードになります．

[proofs/equivalence/Four.v](../proofs/equivalence/Four.v) で [共通ルール](../common/README-ja.md) との一致を証明します．
[proofs/certificates/Four.v](../proofs/certificates/Four.v) で共通定義の下で結果を導きます．

## ビルドと検査

Rocq 9.2 / OCaml 5.3.0，Python 3.11以降，GNU makeを用意し，リポジトリのルートから実行してください．

```text
make check-4x4
```

ルール，証明書，共通定義，4×4の解答の証明をソースからビルドし，カーネルで再検査します．
Gitに収録したソースだけで実行できます．ビルドの既定の出力先は `_build/` です．
健全性・証明書検査・白必勝の各定理に追加公理はありません．
オプションは [ビルド手順](../README-ja.md#checking) を参照してください．

小さい証明書を再生成する場合は次を実行します．

```text
make certificate-4x4
make check-4x4
```

出力先は `4x4/Certificate.v` と `4x4/Certificate.json` です．
黒の手をマス番号順に調べ，白は勝利を保証する最初の手を選びます．同じソースからは同じ証明書が得られます．
