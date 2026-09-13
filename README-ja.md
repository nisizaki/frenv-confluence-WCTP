# FREnvの合流性 — WCTP 2026の検証用成果物

[English](README.md) | 日本語 | [Tagalog](README-tl.md) | [简体中文](README-zh.md)

このリポジトリには、FREnvのβ/σ簡約全体の合流性を示すIsabelle/HOLによる形式化と、それに関連するLean 4による形式化を収録しています。WCTP 2026に投稿する論文に付随する検証用成果物として用意したものです。

**検証結果：** 2026年9月13日、クリーンなGitHub Actionsランナー上で、Isabelle2025-2のビルドとLean 4.33.0のビルド・監査の両方が成功しました。検証した正確なコミットとログは、[検証記録](docs/verification.md)を参照してください。

**二つの形式化は、完成している範囲が異なります。** Isabelleには、簡約全体の合流性定理と、それが依存する定義・定理・補題が含まれています。一方、取り込んだLeanの形式化には、構文、簡約関係、並列簡約に関する証明済みの基盤が含まれていますが、合流性そのものは**まだ証明されていません**。Leanのビルド成功が保証するのは、収録されている宣言の検証であり、残っている合流性の証明課題の解決ではありません。

## ディレクトリ構成

```text
isabelle/
  ROOTS                 必要なソースがそろった四つのセッションを登録
  FREnv/                FREnvの構文、簡約、局所合流性
  EnvEps/               補助計算体系と簡約全体の合流性の移送
  vendor/               必要なAFPのRegular-Sets・Abstract-Rewritingのソース
  docs/                 英語による数学的説明
  README.md             Isabelleのビルド手順と対話的な確認方法
lean/
  lean-toolchain        固定したLeanのバージョン
  lakefile.toml         Lakeプロジェクトの設定
  lake-manifest.json    依存関係のマニフェスト（外部パッケージなし）
  LambdaFrenv.lean      ライブラリのエントリーポイント
  LambdaFrenv/          定義と証明済みの補助補題
  Audit.lean            宣言を確認し、定理が依存する公理を表示
  docs/                 英語の仕様と未解決の証明課題
  README.md             Leanのビルド手順と検証対象の正確な範囲
docs/
  proof-map.md          主な結果、依存関係に沿った証明の流れ、両形式化の相違
  verification.md       検証記録
UPSTREAM.json           元ソースの正確なコミットと元ファイルのハッシュ
PROVENANCE.md           抽出した範囲と成果物としてまとめる際の変更
.github/workflows/      IsabelleとLeanを独立に検証するジョブ
```

## 成果物の取得

```sh
git clone https://github.com/nisizaki/frenv-confluence-WCTP.git
cd frenv-confluence-WCTP
git rev-parse HEAD
```

成果物を引用・評価する際は、完全なコミットハッシュを記録してください。特定の版を再現するには、`git checkout <commit-hash>`を使います。このチェックアウトをビルドするために、サブモジュールや元のリポジトリを別途用意する必要はありません。

## Isabelle/HOLでの検証

[公式インストールページ](https://isabelle.in.tum.de/installation.html)から、使用する環境に対応した**Isabelle2025-2**をインストールしてください。その`bin`ディレクトリを`PATH`に追加し、このリポジトリのルートディレクトリで次を実行します。

```sh
isabelle version
isabelle build -v -j 1 -o threads=2 -o quick_and_dirty=false -D isabelle
```

このコマンドは、同梱したAFPの依存ライブラリ、`FREnv`セッション、および次の最終結果を含む`EnvEps`セッションをビルドします。

```text
FREnv_Full_Confluence_Via_Translation.frenv_beta_sigma_confluent
```

この定理は、同じFREnvの項から始まる任意の二つの有限なβ/σ簡約列の終点が、共通の項へ簡約できることを述べています。環境別の詳細と対話的な確認方法は、[Isabelleの手順](isabelle/README.md)を参照してください。証明の検査は有効になっており、この成果物では`quick_and_dirty`を明示的に無効にしています。

## Lean 4での検証

Leanのツールチェーン管理ツールである[Elan](https://lean-lang.org/install/manual/)をインストールし、`PATH`から`lake`を実行できるようにしてください。その後、次を実行します。

```sh
cd lean
lake env lean --version
lake build
lake env lean Audit.lean
```

リポジトリに収録した`lean-toolchain`は、**leanprover/lean4:v4.33.0**を指定しています。必要に応じて、Elanがこのバージョンをダウンロードします。Mathlibへの依存や、キャッシュのダウンロード手順はありません。証明済みの宣言と、命題の定義と証明との違いについては、[Leanの手順](lean/README.md)を参照してください。

## 結果と対象範囲

| 形式化 | 検証する主な内容 | FREnvの簡約全体の合流性 |
|---|---|---|
| Isabelle/HOL | 補助計算体系の合流性、翻訳、全射性、シミュレーション、持ち上げ、および最終合流性定理 | 記録した、証明検査を有効にしたセッションビルドで検証済み |
| Lean 4 | 定数を含む構文、β/σ簡約、並列簡約、簡約の閉包の合同性、埋め込み、シミュレーション | 取り込んだ版には証明が含まれていない |

両者が扱う言語にも違いがあります。Isabelleは名前として文字列を使い、基本構成要素としての定数を持ちません。Leanは変数と定数を型によってパラメーター化しています。この成果物は、二つの符号化の同値性が証明されているとは主張しません。相違点は[証明の見取り図](docs/proof-map.md)に記載しています。

数学的なMarkdown文書は証明の流れを説明するものですが、その文章自体を機械検証しているわけではありません。由来を追跡できるよう、元の学位論文やロードマップへの参照を残しています。どちらの証明支援系を実行する場合も、学位論文のPDFは不要です。

## 再現性と帰属表示

固定した元リポジトリの版と、成果物としてまとめる際の変更は[PROVENANCE.md](PROVENANCE.md)、ファイル単位の元ソース一覧は[UPSTREAM.json](UPSTREAM.json)、実際の検証結果は[docs/verification.md](docs/verification.md)を参照してください。二つのGitHub Actionsジョブは、クリーンなランナー上でビルドコマンドを繰り返し実行します。

同梱したAFPのソースには、著作者とライセンスに関する表示を保持しています。[依存ライブラリの注意事項](isabelle/vendor/README.md)を参照してください。この抽出によって、元の形式化全体に新たな一括ライセンスを付与するものではありません。
