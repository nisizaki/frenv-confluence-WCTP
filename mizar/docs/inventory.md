# 成果物一覧と三つの証明支援系の規模比較

> This document was written in the standalone development repository
> [nisizaki/frenv-mizar](https://github.com/nisizaki/frenv-mizar), where the
> articles live in `text/` and the vocabularies in `dict/` — the same layout as
> `mizar/` here. It is reproduced unchanged except for the links, so a few file
> names it mentions belong to that repository: its `build.sh` corresponds to
> `verify.sh` here. The document is in Japanese.

本リポジトリ（Mizar）で作成したファイルの一覧と、参照実装
[nisizaki/frenv-confluence-WCTP](https://github.com/nisizaki/frenv-confluence-WCTP)
の Isabelle/HOL 版・Lean 4 版の規模を並べたもの。

行数は `wc -l`、文字数は `wc -m`（UTF-8 の文字数。バイト数ではない）。
計測日 2026-09-15。

---

## 1. 今回作成した成果物（Mizar）

2026-09-15 の二度の改訂（合同閉包への再構成、および中置記法の導入）を反映した
現在の構成。

### 1.1 証明スクリプト（article）

| ファイル | 行数 | 文字数 | 定理数 | 内容 |
|---|---:|---:|---:|---|
| `text/envsyn.miz` | 1,258 | 45,054 | 26 | λ_EnvEps の構文、構造帰納法・構造再帰スキーム、項上の関係、中置記法 |
| `text/envlen.miz` | 388 | 13,072 | 15 | 長さ測度 |
| `text/envcc.miz` | 1,709 | 65,612 | 30 | 合同閉包 `CC Q` の一般論 |
| `text/envsig.miz` | 2,631 | 98,096 | 56 | σ の根規則、σ 簡約、16 規則、反転、頭部別反転、長さ減少、停止性 |
| `text/envbeta.miz` | 1,942 | 71,734 | 61 | β の根規則、β 簡約と βσ 簡約、19 規則、反転、頭部別反転 |
| `text/envpeak.miz` | 2,225 | 102,270 | 12 | 8 つの根規則ピーク、合成のピーク、局所合流性、σ の合流性 |
| `text/envnf.miz` | 636 | 24,669 | 19 | σ 正規形とその文法、正規形関手 `snf` |
| `text/envpar.miz` | 2,678 | 111,482 | 34 | 並行簡約、三角性質、ダイヤモンド性、β の合流性 |
| `text/envkey.miz` | 1,461 | 61,436 | 30 | 合成両立性、鍵補題 |
| `text/envconf.miz` | 421 | 15,182 | 13 | Hardin の解釈法、λ_EnvEps の完全合流性 |
| `text/frenv_1.miz` | 818 | 29,699 | 17 | λ_FREnv の構文 |
| `text/frenv_2.miz` | 1,099 | 39,756 | 25 | λ_FREnv の βσ 簡約 |
| `text/frenv_3.miz` | 800 | 28,090 | 20 | 翻訳、再帰等式、全射性、逆転 |
| `text/frenv_4.miz` | 463 | 19,593 | 3 | simulation |
| `text/frenv_5.miz` | 880 | 36,133 | 8 | lifting、λ_FREnv の完全合流性 |
| **小計（15 本）** | **19,409** | **761,878** | **369** | |

### 1.2 語彙ファイル

| ファイル | 行数 | 文字数 |
|---|---:|---:|
| `dict/envsyn.voc` | 15 | 116 |
| `dict/envlen.voc` | 2 | 17 |
| `dict/envcc.voc` | 2 | 16 |
| `dict/envsig.voc` | 2 | 21 |
| `dict/envbeta.voc` | 4 | 48 |
| `dict/envnf.voc` | 1 | 5 |
| `dict/envpar.voc` | 3 | 35 |
| `dict/envconf.voc` | 1 | 8 |
| `dict/frenv_1.voc` | 9 | 67 |
| `dict/frenv_2.voc` | 2 | 18 |
| `dict/frenv_3.voc` | 5 | 27 |
| **小計（11 本）** | **46** | **378** |

### 1.3 スクリプト・文書

| ファイル | 行数 | 文字数 | 内容 |
|---|---:|---:|---|
| `check.sh` | 7 | 169 | article 1 本を検証しエラーファイルを表示 |
| `build.sh` | 20 | 655 | 全 article を依存順に検証し `prel/` へ書き出す |
| `README.md` | 193 | 9,327 | 主定理、article 一覧、証明の骨格、設計方針 |
| `WORKLOG.md` | 651 | 27,083 | 指示の逐語引用と作業記録（開始/終了時刻つき） |
| `TIMELINE.md` | 133 | 5,313 | 段階ごとの所要時間と時間的推移 |
| `INVENTORY.md` | 286 | 10,236 | 本文書 |

### 1.4 Mizar 側合計

| 区分 | ファイル数 | 行数 | 文字数 |
|---|---:|---:|---:|
| 証明スクリプト（`.miz` + `.voc`） | 26 | 19,455 | 762,256 |
| ビルドスクリプト | 2 | 27 | 824 |
| 文書 | 4 | 1,263 | 51,959 |
| **総計** | **32** | **20,745** | **815,039** |

### 1.5 検証

Mizar Ver. 8.1.15 (Linux/FPC)、MML 5.99。`prel/` と中間ファイルを全削除した
状態から `./build.sh` を実行し、15 記事すべてが検証を通る（1 分 30 秒、
`.err` は全本 0 バイト）。主定理の偽の変種（`FrRed(V) is empty`）は error 4
で拒否されることも確認済み。

---

## 2. Isabelle/HOL 版（参照実装）

### 2.1 `isabelle/EnvEps/` — λ_EnvEps とその翻訳

| ファイル | 行数 | 文字数 |
|---|---:|---:|
| `EnvEps_Syntax.thy` | 33 | 942 |
| `EnvEps_Term_Length.thy` | 28 | 958 |
| `EnvEps_Sigma.thy` | 57 | 2,355 |
| `EnvEps_Sigma_Congruence.thy` | 101 | 5,651 |
| `EnvEps_Sigma_Length_Decrease.thy` | 71 | 1,739 |
| `EnvEps_Sigma_Termination.thy` | 30 | 1,156 |
| `EnvEps_Sigma_Root_Peaks.thy` | 584 | 26,876 |
| `EnvEps_Sigma_Assoc_Peak.thy` | 168 | 7,891 |
| `EnvEps_Sigma_Inner_Peaks.thy` | 152 | 6,509 |
| `EnvEps_Sigma_Local_Confluence.thy` | 88 | 3,447 |
| `Newmans_Lemma.thy` | 58 | 2,576 |
| `EnvEps_Sigma_Confluence.thy` | 24 | 1,102 |
| `EnvEps_Sigma_Normal_Form.thy` | 115 | 4,662 |
| `EnvEps_Sigma_Normal_Form_Grammar.thy` | 181 | 7,436 |
| `EnvEps_Sigma_Nf_Equiv.thy` | 146 | 6,479 |
| `EnvEps_Beta_Step.thy` | 65 | 2,905 |
| `EnvEps_BetaSigma.thy` | 71 | 3,104 |
| `EnvEps_BetaSigma_Congruence.thy` | 61 | 3,610 |
| `EnvEps_Beta_Over_Sigma.thy` | 62 | 3,381 |
| `EnvEps_Beta_Over_Sigma_Congruence.thy` | 273 | 15,297 |
| `EnvEps_Beta_Over_Sigma_Confluence.thy` | 76 | 3,916 |
| `EnvEps_Beta_Normal_Form_Simulation.thy` | 275 | 15,524 |
| `EnvEps_Complete_Development.thy` | 34 | 1,581 |
| `EnvEps_Parallel_Reduction.thy` | 64 | 3,568 |
| `EnvEps_Parallel_Reduction_Reflexivity.thy` | 84 | 2,798 |
| `EnvEps_Parallel_Reduction_Soundness.thy` | 307 | 16,594 |
| `EnvEps_Parallel_Reduction_Simulation.thy` | 166 | 8,371 |
| `EnvEps_Parallel_Reduction_Triangle_Property.thy` | 304 | 17,247 |
| `EnvEps_Parallel_Reduction_Composition_Compatibility.thy` | 524 | 30,404 |
| `EnvEps_Parallel_Reduction_Confluence.thy` | 38 | 1,692 |
| `Diamond_Implies_Confluence.thy` | 82 | 4,155 |
| `EnvEps_Beta_Sigma_Full_Confluence.thy` | 102 | 4,901 |
| `EnvEps_FREnv_Translation.thy` | 24 | 1,395 |
| `EnvEps_FREnv_Translation_Surjective.thy` | 27 | 1,082 |
| `EnvEps_FREnv_Translation_Inversion.thy` | 63 | 3,149 |
| `EnvEps_FREnv_Translation_Simulation.thy` | 119 | 4,710 |
| `EnvEps_FREnv_Translation_Lifting.thy` | 458 | 32,508 |
| `EnvEps_FREnv_Translation_Multi_Step_Lifting.thy` | 62 | 3,067 |
| `FREnv_Full_Confluence_Via_Translation.thy` | 69 | 3,885 |
| **小計（39 本）** | **5,246** | **268,623** |

### 2.2 `isabelle/FREnv/` — λ_FREnv の直接展開

| ファイル | 行数 | 文字数 |
|---|---:|---:|
| `FREnv_Syntax.thy` | 37 | 1,191 |
| `FREnv_Sigma.thy` | 58 | 2,482 |
| `FREnv_BetaSigma.thy` | 69 | 3,257 |
| `FREnv_BetaSigma_Congruence.thy` | 50 | 2,843 |
| `FREnv_BetaSigma_Root_Peaks.thy` | 490 | 26,118 |
| `FREnv_BetaSigma_Assoc_Peak.thy` | 155 | 8,683 |
| `FREnv_BetaSigma_DApp_Peak.thy` | 242 | 13,698 |
| `FREnv_BetaSigma_Congruence_Peaks.thy` | 401 | 23,955 |
| `FREnv_BetaSigma_Local_Confluence.thy` | 74 | 2,811 |
| **小計（9 本）** | **1,576** | **85,038** |

### 2.3 セッション定義・外部ライブラリ・文書

| 区分 | ファイル数 | 行数 | 文字数 | 備考 |
|---|---:|---:|---:|---|
| `ROOT` / `ROOTS` | 3 | 70 | 2,316 | セッション定義 |
| `vendor/`（AFP 由来） | 18 | 9,071 | 369,762 | `Abstract-Rewriting`, `Regular-Sets`。第三者のコードで、本プロジェクトの著作ではない |
| `docs/` + `README.md` | 33 | 3,274 | 245,138 | 仕様文書（Markdown）。証明スクリプトではない |

### 2.4 Isabelle 側合計

| 区分 | ファイル数 | 行数 | 文字数 |
|---|---:|---:|---:|
| 自作の証明スクリプト（`.thy` + `ROOT`） | 51 | 6,892 | 355,977 |
| 外部ライブラリ（AFP vendored） | 18 | 9,071 | 369,762 |
| 上記 2 つの合計 | 69 | 15,963 | 725,739 |

---

## 3. Lean 4 版（参照実装）

### 3.1 証明スクリプト

| ファイル | 行数 | 文字数 | 内容 |
|---|---:|---:|---|
| `LambdaFrenv.lean` | 13 | 420 | ルートモジュール |
| `LambdaFrenv/Basic.lean` | 167 | 5,803 | λ_FREnv の構文、βσ 簡約、合流性の枠組み |
| `LambdaFrenv/Rewriting.lean` | 142 | 5,364 | 抽象書き換え系の基本（Mathlib 非依存のため自前） |
| `LambdaFrenv/EnvEps/Syntax.lean` | 269 | 10,773 | λ_EnvEps の構文と σ 簡約 |
| `LambdaFrenv/EnvEps/Length.lean` | 156 | 5,625 | 長さ測度と停止性 |
| `LambdaFrenv/EnvEps/SigmaConfluence.lean` | 289 | 10,689 | σ の局所合流性・合流性 |
| `LambdaFrenv/EnvEps/NormalForm.lean` | 232 | 8,777 | σ 正規形とその文法 |
| `LambdaFrenv/EnvEps/PStep.lean` | 224 | 8,711 | 並行簡約 |
| `LambdaFrenv/EnvEps/Compat.lean` | 384 | 18,286 | 合成両立性・鍵補題 |
| `LambdaFrenv/EnvEps/BetaOverSigma.lean` | 141 | 5,402 | β over σ、λ_EnvEps の完全合流性 |
| `LambdaFrenv/Par.lean` | 357 | 15,761 | λ_FREnv 側の並行簡約 |
| `LambdaFrenv/ParNotStrong.lean` | 147 | 5,808 | 並行簡約が強合流でないことの反例（否定的結果） |
| `LambdaFrenv/Translation.lean` | 351 | 14,906 | 翻訳・全射性・simulation・lifting・合流性 |
| `LambdaFrenv/Confluence.lean` | 38 | 1,215 | 主定理のまとめ |
| `Audit.lean` | 46 | 1,852 | 公理・`sorry` の不使用を機械的に検査 |
| **小計（15 本）** | **2,956** | **119,392** |

### 3.2 設定・文書

| 区分 | ファイル数 | 行数 | 文字数 |
|---|---:|---:|---:|
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | 3 | 13 | 277 |
| `docs/` + `README.md` | 5 | 661 | 23,574 |

---

## 4. 三つの証明支援系の比較

### 4.1 自作の証明スクリプトのみ（仕様文書・外部ライブラリを除く）

| 証明支援系 | ファイル数 | 行数 | 文字数 | 行数比 | 文字数比 | 1 行あたり文字数 |
|---|---:|---:|---:|---:|---:|---:|
| Mizar（`.miz` + `.voc`） | 26 | 19,455 | 762,256 | 6.58 | 6.38 | 39.2 |
| Isabelle/HOL（`.thy` + `ROOT`） | 51 | 6,892 | 355,977 | 2.33 | 2.98 | 51.6 |
| Lean 4（`.lean`） | 15 | 2,956 | 119,392 | 1.00 | 1.00 | 40.4 |

「行数比」「文字数比」は Lean 4 を 1 としたときの倍率。

### 4.2 依存ライブラリを含めた場合

抽象書き換え系（合流性・停止性・Newman の補題・正規形）をどこから得るかが
三者で異なるため、その扱いによって比較の姿が変わる。

| 証明支援系 | 抽象書き換え系の調達 | 行数（自作） | 行数（ライブラリ込み） |
|---|---|---:|---:|
| Mizar | MML の `REWRITE1` をそのまま使用（本リポジトリには含まれない） | 19,455 | 19,455 |
| Isabelle/HOL | AFP の `Abstract-Rewriting` をリポジトリに vendoring | 6,892 | 15,963 |
| Lean 4 | Mathlib を使わず `Rewriting.lean`（142 行）を自前で用意 | 2,956 | 2,956 |

vendoring した AFP を含めると Isabelle 版は 15,963 行・725,739 文字となり、
Mizar 版（19,455 行・762,256 文字）と同じ桁に収まる。
Mizar 版が MML の `REWRITE1` に依存している分を勘定に入れると、
実質的な差は「Mizar ≈ Isabelle ≫ Lean」に近い。

### 4.3 仕様文書を含めた総計

| 証明支援系 | 証明 | 文書 | その他 | 総行数 | 総文字数 |
|---|---:|---:|---:|---:|---:|
| Mizar | 19,455 | 1,263 | 27 | 20,745 | 815,039 |
| Isabelle/HOL（vendor 除く） | 6,892 | 3,274 | — | 10,166 | 601,115 |
| Lean 4 | 2,956 | 661 | 13 | 3,630 | 143,243 |

Isabelle 版の `docs/` 32 本（3,209 行・241,542 文字）は、λ_EnvEps と λ_FREnv の
構文・簡約規則・各補題の非形式的な仕様を記した Markdown で、三つの形式化すべての
出発点になっている文書群である。Lean 版の `docs/` はその部分集合 4 本。
Mizar 版はこれらを新規には書かず、参照実装の文書を読んで形式化した。

---

## 5. 比較を読むときの注意

数字をそのまま「冗長さの比」と読むことはできない。以下の違いがある。

**(a) 証明した命題の範囲が違う**

- Isabelle 版は、翻訳経由の λ_FREnv 合流性（`EnvEps/` 側）に加えて、
  `FREnv/` で λ_FREnv の βσ 簡約の**局所**合流性を直接展開している
  （1,576 行）。Mizar 版と Lean 版にはこの層がない。
- Lean 版は並行簡約が強合流でないことの反例（`ParNotStrong.lean`、147 行）を
  含む。Mizar 版と Isabelle 版にはない。
- Lean 版のみ定数 `c` と規則 `ε(c)M → c` を持つ。Isabelle 版と Mizar 版は持たない。
- 変数の型の扱いが違う。Isabelle 版は `type_synonym name = string` と文字列に
  固定しているが、Lean 版は型パラメータ `V`、Mizar 版は任意の空でない集合 `V`
  をパラメータとしている。

**(b) 行の長さの規約が違う**

Mizar は 1 行 80 文字の上限があり、本リポジトリでは 74 文字前後で折り返して
いる。1 行あたり文字数は Mizar 40.6、Lean 40.4 に対し Isabelle は 51.6 で、
Isabelle は 1 行が長い。行数より文字数で見るほうが実態に近い。

**(c) 自動化の量が違う**

Isabelle は `auto`/`blast`/`metis` などの自動証明器が場合分けの大半を片付け、
Lean は `simp`/`omega` に加えて `cases ... <;> simp_all` のような組み合わせ子で
多数のケースを一度に閉じられる。Mizar には自動証明器がなく、推論は 1 段ずつ
明示的に書く必要がある。とくに、16 規則にわたる反転補題・命名・多段合同則の
ような定型部分は、Mizar では規則ごとに数十行ずつを書き出すことになる。
本リポジトリではその部分を Python の生成スクリプトで書き出しているが、
生成された行はそのまま行数に計上されている。

**(d) 帰納的定義の有無**

Mizar には帰納的データ型も帰納的述語もない。項は `DTCONSTR` の構文解析木として
構成し（`envsyn`）、簡約関係は「規則で閉じた最小の関係」として定義したうえで、
反転補題を別途証明する必要がある。Isabelle の `datatype` + `inductive` と
Lean の `inductive` は、これらを宣言 1 つで与え、場合分け・帰納法・反転を
自動生成する。Mizar 版の行数が大きい主因はここにある。

2026-09-15 の改訂で、この定型作業は 2 つの部品に括り出した。構造再帰は
`ENVSYN:sch 2` として一度だけ証明され、合同閉包の一般論（合同規則・反転・
頭部別反転・多段合同則・単調性・和との可換性）は `envcc` で一度だけ証明されて
σ・β・βσ の 3 つの簡約関係で共有される。

行数は減っていない（17,717 → 17,659 → 19,409）。減ったのは重複であって行数では
なく、最後の増加は頭部別反転を明示的な 16 ケースの場合分けに書き下したためで
ある。読みやすさを優先した結果としてそうしている。
