# 証明書ソースの取得と検査

[English](README.md) | [日本語](README-ja.md)

4×4の証明は，Git内のファイルだけでビルド・検査できます．
**6×6には，以下の5個の証明書ソースアーカイブも全て必要です．**
これらには，主定理で使う戦略データと証明が含まれます．
配布物はソースだけで，`.vo` やコンパイル済みプラグインは含みません．

<a id="certificate-archives"></a>

## 証明書ソースを取得する

リポジトリの [Releasesページ](https://github.com/ksk/tppmark2026-othello/releases)を開き，手元のソースと同じ版のReleaseを選んでください．
添付ファイルから以下の5個全てを，一つのディレクトリにダウンロードします．
GitHubが自動生成する「Source code」のダウンロードには，Git内のファイルだけが含まれ，これらの証明書アーカイブは含まれません．

| ファイル | バイト数 |
|---|---:|
| `tppmark2026-othello-6x6-certificates-01-of-05.tar.gz` | 586,962,086 |
| `tppmark2026-othello-6x6-certificates-02-of-05.tar.gz` | 550,625,706 |
| `tppmark2026-othello-6x6-certificates-03-of-05.tar.gz` | 600,701,274 |
| `tppmark2026-othello-6x6-certificates-04-of-05.tar.gz` | 608,348,504 |
| `tppmark2026-othello-6x6-certificates-05-of-05.tar.gz` | 568,892,691 |

圧縮ファイルの合計は **2,915,530,261バイト（約2.92 GB）** です．
それぞれ独立した `.tar.gz` で，5個全てが必要です．連結する必要はありません．
正確なサイズとSHA-256は，[アーカイブの記録](archives.json)にあります．
確認コマンドは，手元のソースに含まれるこの記録と [certificates.tsv](certificates.tsv) を使います．
Releaseにも添付されている `archives.json`・`certificates.tsv`・[SHA256SUMS](SHA256SUMS) のダウンロードは，これらのコマンドには不要です．

## 確認して展開する

Python 3.11以降とGNU makeを使用し，リポジトリのルートから実行します．
`/path/to/archives` はダウンロードしたファイルの保存先に置き換えてください．
展開せずにサイズとSHA-256を確認するには，次を実行します．

```text
make check-archives ARCHIVE_DIR=/path/to/archives
```

全アーカイブを確認した上で展開し，各ファイルを収録一覧と照合するには，次を実行します．

```text
make unpack-certificates ARCHIVE_DIR=/path/to/archives
```

展開コマンドにもアーカイブの確認が含まれるため，確認だけのコマンドを先に実行する必要はありません．
別途 `tar` やチェックサム用のプログラムを用意する必要はありません．
`6x6/` の下に，次の4個のディレクトリを作成します．

| ディレクトリ | 内容 |
|---|---|
| `6x6/InitialLower/`・`6x6/InitialUpper/` | `Goal.v`，`B*.v`，`Links.v`，`Result.v`，ビルド用manifest |
| `6x6/InitialLowerCompact/`・`6x6/InitialUpperLocalCompact/` | `D*.v`，`E*.v`，`K*.v`，`Links.v`，ビルド用manifest |

一覧には **8,376ファイル（Rocqソース8,372個とJSONのビルド用manifest 4個）** があり，展開後の合計は **8,924,569,050バイト（約8.92 GB）** です．
ビルド用manifestは，証明書のブロックと依存関係を列挙しています．
生成元を示す `source`・`meeting_line` に元の探索で使ったファイル名がある場合もありますが，その探索DBや対局のJSONファイルはビルドの入力ではありません．
結合用manifestの `source` は，アーカイブ内のブロックディレクトリを参照します．

4個の証明書ディレクトリのいずれかが既にある場合，展開は停止します．
ソースを用意済みなら展開を省略し，`make check-certificate-files` で確認してください．
別の場所へ展開するには，`CERTIFICATE_SOURCE=/path/to/sources` を追加し，ビルドと証明書ファイルの検査にも同じ指定を使います．
`6x6/InitialLower/` などの証明書ディレクトリがある親ディレクトリを指定してください．

展開すると約8.92 GBのソースを書き出します．途中の未圧縮アーカイブや，ソースの複製は作りません．
展開プログラムは，ソースの容量に1 GBを加えた空き容量を必要とします．これは展開だけの見積もりで，ビルドには以下のより大きな容量が必要です．
展開と照合に成功した後は，ダウンロードしたアーカイブを削除して容量を空けられます．展開した証明書ソースは全てビルド用に残してください．

## 証明をビルドして検査する

**6×6の初回のビルド・証明検査には数時間を見込んでください．**
[ルートのビルド手順](../README-ja.md#checking)にあるツールチェインと設定を使います．
6×6の初回ビルドには，**展開後に70 GB以上の空き容量**を確保してください．
ダウンロードと展開の前には，**約80 GBと，アーカイブ用の2.92 GB**を見込みます．ツールチェインとOSのスワップ使用量は含みません．
実測サイズと見積もりの意味は，[ディスク使用量の説明](../README-ja.md#disk-use)を参照してください．

証明書ソースを用意したら，両サイズを次のコマンドで検査できます．

```text
make check-disk
make check-certificate-files
make check
```

6×6だけの場合は `make check-6x6` を使います．
空き容量とファイルの照合では証明を検査しません．ビルド時にRocqが証明をコンパイルして検査します．
オブジェクト，プラグイン，ログの出力先は既定では `_build/` です．別の場所は `BUILD_DIR=/path/to/build` で指定できます．
ビルド先は証明書ソースと同じファイルシステムに置く必要があります．ソースをハードリンクすることで，さらに8.92 GBをコピーせずに済みます．
同じコマンドでビルドを再開できます．新規または空のビルド先を要求する場合は `FRESH=1` を追加してください．
別途実行できる全体の公理監査とカーネルによる再検査については，[6×6の説明](../6x6/README-ja.md)を参照してください．

## 収録一覧と検証記録

| ファイル | 内容 |
|---|---|
| [git-files.txt](git-files.txt) | リポジトリに含まれるソースファイル |
| [certificates.tsv](certificates.tsv) | 証明書ソースのパス，サイズ，SHA-256 |
| [archives.json](archives.json) | アーカイブのサイズ，SHA-256，ファイルの整合性検査 |
| [SHA256SUMS](SHA256SUMS) | Releaseの添付ファイルのチェックサム |
| [verification.json](verification.json) | ツールチェイン，証明の検証範囲，ビルドの実測値，未実施の検査 |

リポジトリの収録一覧と日英READMEの組を確認するには，次を実行します．

```text
make review-files
```

このコマンドは，大きな証明書ファイルの読み取りや証明の検査を行いません．
展開済みのソースは `make check-certificate-files`，ダウンロードしたファイルは `make check-archives ARCHIVE_DIR=/path/to/archives` で確認します．
文書の検査では，コマンド，識別子，リンク，記録したファイルのハッシュを照合します．翻訳の意味が一致することまでは確認できません．

探索DB，チェックポイント，中間JSONL，元の6×6の探索・変換プログラムは含まれません．
ビルドでは，収録した証明書ソースから証明を検査します．ゲーム木を探索して証明書を再生成するものではありません．
生成元については，[6×6の証明書の説明](../6x6/README-ja.md#certificate-data)を参照してください．
