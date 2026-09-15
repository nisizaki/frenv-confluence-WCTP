# frenv-mizar 作業記録 (WORKLOG)

> This document was written in the standalone development repository
> [nisizaki/frenv-mizar](https://github.com/nisizaki/frenv-mizar), where the
> articles live in `text/` and the vocabularies in `dict/` — the same layout as
> `mizar/` here. It is reproduced unchanged except for the links, so a few file
> names it mentions belong to that repository: its `build.sh` corresponds to
> `verify.sh` here. The document is in Japanese.

Mizar による形式化作業の記録。ユーザ指示は逐語で引用し、各作業の開始/終了時刻を記す。
時刻はすべて JST。

段階ごとの所要時間のまとめは [timeline.md](timeline.md) にある。

## 作業環境

- 作業ディレクトリ: `~/local/prog/frenv-mizar`（WSL/Ubuntu 側。Windows 側は使用しない）
- Mizar: Ver. 8.1.15 (Linux/FPC)、`/usr/local/bin/`
- `MIZFILES=/usr/local/share/mizar`（`~/.bashrc` にのみ設定。非対話シェルでは明示指定が必要）
- 検証コマンド: `export MIZFILES=/usr/local/share/mizar; mizf text/<name>.miz`

---

## 2026-09-15

### 指示 1

> WSL/Ubuntuにはproof checker Mizarをインストールしました。あなたが使えるかどうか確認してください。

| 開始 | 終了 | 種別 | 内容 |
|---|---|---|---|
| 02:14 | 02:16 | 環境調査 | `mizf`/`verifier`/`accom`/`makeenv`/`miz2prel` が `/usr/local/bin` に存在することを確認。バージョンは Mizar 8.1.15 (Linux/FPC)。`MIZFILES=/usr/local/share/mizar`、MML 1515 ファイル、`prel/` は a–z の 26 ディレクトリ、requirements の `.dre`（NUMERALS/REAL/SUBSET/ARITHM/BOOLE/HIDDEN）も揃っていることを確認。 |
| 02:16 | 02:17 | Mizar 実行（正例） | `~/mizar_test/text/tst2.miz`（`X c= Y & Y c= X implies X = Y`、`XBOOLE_0:def 10`）を `mizf` で検証 → エラー 0 件。 |
| 02:16 | 02:17 | Mizar 実行（正例） | 実数の命題 `for a, b being Real st a <= b holds a + 1 <= b + 1`（`XREAL_1:6`）を新規作成し検証 → エラー 0 件。最初に `constructors` 不足で `**** Internal Error ****` + エラー 825 (Cannot find constructors name on constructor list) が出たため、環境部に `NUMBERS, XXREAL_0, ARYTM_3` を追加して解決。 |
| 02:17 | 02:17 | Mizar 実行（負例） | 上記の結論を `a + 1 < b + 1` に改変 → `.err` に `12 54 4` = 「This inference is not accepted」を検出。エラー報告が正しく機能することを確認。 |

**結論:** Mizar は利用可能。MML 参照・requirements 解決・推論チェック・エラー報告のすべてが動作する。

### 指示 2

> 2の選択肢は、Windows側の作業ディレクトリは使わなくて、WSL/Ubuntu側の作業ディレクトリをつかってください。たとえば、~/local/progのしたにfrenv-mizarというディレクトリを作って、その下にtextやdictをおいていただいてかまいません。

| 開始 | 終了 | 種別 | 内容 |
|---|---|---|---|
| 02:17 | 02:20 | 環境構築 | `~/local/prog/frenv-mizar/{text,dict}` を作成。動作確認用 `text/tst1.miz`（実数の命題）を配置し `mizf` で検証 → エラー 0 件。`git init`、`.gitignore`（Mizar 中間ファイルを除外し `.miz` のみ追跡）、本 WORKLOG.md を作成。 |

### 指示 3

> 新規に nisizaki/frenv-mizar を作ってください。GitHubの操作のためにはWSL/Ubuntuのghコマンドを使ってください。

| 開始 | 終了 | 種別 | 内容 |
|---|---|---|---|
| 02:19 | 02:21 | リポジトリ作成 | WSL の `gh` (v2.46.0, 認証済みアカウント nisizaki) で `gh repo create nisizaki/frenv-mizar --private --source=. --push` を実行。リモート `origin` を設定し `main` ブランチを push。公開設定は他の研究リポジトリに合わせて private とした。 |

**リモート:** https://github.com/nisizaki/frenv-mizar (private)

### 指示 4

> GitHubリポジトリ
> https://github.com/nisizaki/frenv-confluence-WCTP
> のディレクトリ isabelleに$\lambda_{\mathrm{FREnv}}$の合流性のIsabelle/HOLにおける形式的証明があり、ディレクトリleanには、Lean4における形式的証明があります。docsディレクトリには、関連文書があります。これらを読んでください。

| 開始 | 終了 | 種別 | 内容 |
|---|---|---|---|
| 02:21 | 02:24 | 資料読解 | `gh repo clone` で `~/local/prog/frenv-confluence-WCTP` に取得（既存のため `git pull`）。下記を読了。 |

読んだファイル:

- **全体文書**: `README.md`, `PROVENANCE.md`, `docs/proof-map.md`, `docs/theory-index.md`, `docs/verification.md`
- **Isabelle 中核**: `FREnv_Syntax`, `FREnv_Sigma`, `FREnv_BetaSigma`, `EnvEps_Syntax`, `EnvEps_Sigma`, `EnvEps_BetaSigma`, `EnvEps_Beta_Step`, `EnvEps_Term_Length`, `EnvEps_Sigma_Length_Decrease`, `EnvEps_Sigma_Termination`, `Newmans_Lemma`, `Diamond_Implies_Confluence`, `EnvEps_Sigma_Local_Confluence`, `EnvEps_Sigma_Confluence`, `EnvEps_Sigma_Normal_Form`, `EnvEps_Sigma_Normal_Form_Grammar`, `EnvEps_Complete_Development`, `EnvEps_Parallel_Reduction`, `EnvEps_Parallel_Reduction_Reflexivity`, `EnvEps_Parallel_Reduction_Confluence`, `EnvEps_Beta_Over_Sigma`, `EnvEps_Beta_Over_Sigma_Confluence`, `EnvEps_Beta_Sigma_Full_Confluence`, `EnvEps_FREnv_Translation` と Inversion / Simulation / Surjective / Lifting / Multi_Step_Lifting, `FREnv_Full_Confluence_Via_Translation`。大型の証明本体（Triangle_Property 17KB, Composition_Compatibility 30KB, Sigma_Root_Peaks 27KB, Translation_Lifting 32KB 等）は冒頭の解説と定理文のみ確認。
- **Lean**: `LambdaFrenv.lean`, `Basic.lean`, `Rewriting.lean`, `Confluence.lean`, `Audit.lean`, `EnvEps/Syntax.lean` は全文。`Length` / `NormalForm` / `PStep` / `Compat` / `BetaOverSigma` / `SigmaConfluence` / `Translation` / `Par` / `ParNotStrong` は解説ヘッダと宣言一覧。
- **数学的文書**: `isabelle/docs/frenv-syntax.md`, `frenv-reduction-sigma.md`, `frenv-reduction-beta-sigma.md`, `frenv-beta-sigma-full-confluence.md`

読解結果の要点:

- 最終定理は Isabelle の `FREnv_Full_Confluence_Via_Translation.frenv_beta_sigma_confluent`、Lean の `LambdaFrenv.frenv_beta_sigma_confluent`。いずれも 2026-09-13 に CI で検証済（Isabelle2025-2 / Lean 4.33.0、commit 725b0b6）。
- 証明経路: λ_FREnv では `App (Eps M) N` が環境合成と関数適用を兼ねるため σ の停止性が直接示せない。合成 `Comp` を原始構成子に持つ補助計算系 λ_EnvEps を導入し、(1) 乗法的長さ測度で σ の停止性、(2) 臨界対解析で σ の局所合流性、(3) Newman の補題で σ の合流性、(4) σ 正規形の文法、(5) 並行簡約の三角性質（完全展開 cd 経由）で β/σ 上の合流性、(6) λ_EnvEps 全体の合流性、(7) 翻訳の全射性・simulation・multi-step lifting で λ_FREnv へ移送、という順。
- λ_FREnv の並行簡約はダイヤモンド性を持たない。Lean の `not_parStronglyConfluent` が結合律五角形 `((v∘v)∘v)∘v` で反証済み。σ 正規化を経由せざるを得ないのはこのため。
- Isabelle 版は変数を string とし定数を持たない。Lean 版は変数型 V・定数型 C でパラメタ化し `const` 構成子と対応する規則を持つ。両者の符号化の同値性は証明されていない。
- 形式化の過程で、文書の臨界対列挙 (2.21)-(2.31) に漏れ（Assoc 内の DExtn）が発見されている（`EnvEps_Sigma_Assoc_Peak` 冒頭に記載）。

### 指示 5

> ではBで形式化を始めてください。また、GitHubリポジトリ
> https://github.com/nisizaki/frenv-mizar
> にこの作業の記録や成果をpushしてください。

選択肢 B = 「構文と σ 簡約の定義＋停止性（長さ測度）まで」。対象は λ_EnvEps（λ_FREnv 側では σ の停止性が直接には示せないため。合流性証明が補助計算系 λ_EnvEps を経由するのと同じ理由）。

| 開始 | 終了 | 種別 | 内容 |
|---|---|---|---|
| 02:25 | 02:30 | MML 調査 | 抽象書き換え系 `REWRITE1`（Newman の補題が登録 `strongly-normalizing locally-confluent -> confluent` として存在）、項代数のための `DTCONSTR`（`TS(G)`・構造帰納法 sch 7・構造再帰 sch 8）、`TREES_1`–`TREES_4`、`LANG1` を確認。Mizar には帰納的データ型がないため DTCONSTR の構文解析木で項を表現する方針を決定。 |
| 02:30 | 02:36 | Mizar 記述 | 記号アルファベット `EnvEpsSym`、文法 `EnvEpsGram`（存在性・一意性を DTCONSTR sch 1/2 で）、記号の所属補題、`x ==> p` の型補題、終端/非終端記号の特徴づけ（Th5）。検証通過。 |
| 02:36 | 02:44 | Mizar 記述 | 文法が `with_terminals with_nonterminals with_useful_nonterminals` であることを登録。`mode EnvEpsTerm of V`（= `Element of TS(EnvEpsGram(V))`）を定義。7 構成子 `eVar eId eLam eEps eApp eComp eExt` を定義し、いずれも `TS` に属することを証明。検証通過。 |
| 02:44 | 02:48 | Mizar 記述 | 根記号の値（Th9）、構成子の相互相異（Th10、21 対）、単射性（Th11–Th16）、場合分け定理（Th17：任意の項は 7 形のいずれか）。検証通過。 |
| 02:48 | 02:53 | Mizar 記述 | 構造帰納法スキーム `EnvEpsInd` を DTCONSTR sch 7 から導出。検証通過。 |
| 02:53 | 03:05 | Mizar 記述 | 長さ測度。DTCONSTR sch 8 の `NTermVal` が `Element of D()` 型を要求するため、任意オブジェクトから自然数を取り出す補助関手 `natsel` を定義（`In` と `.` の型不整合の回避）。`EnvEpsLen(V)` を構造再帰で定義し、`elen M` を導入。途中、`DTCONSTR:sch 8` が解決できない不具合は `constructors` に `CARD_3, FINSEQOP, FINSEQ_4, FINSOP_1, PRE_POLY` が欠けていたためと判明し追加。検証通過。 |
| 03:05 | 03:10 | Mizar 記述 | `IFEQ` 連鎖の評価補題（Th24）と 7 つの漸化式（Th25–Th30）: `elen(eVar v) = 1`, `elen(eId V) = 1`, `elen(eLam(v,M)) = 2*elen M`, `elen(eEps M) = 2*elen M`, `elen(eApp(M,N)) = elen M + elen N + 1`, `elen(eExt(M,v,N)) = elen M + elen N + 1`, `elen(eComp(M,N)) = elen M * (elen N + 1)`。測度の正値性（Th31）を構造帰納法で証明。検証通過。 |
| 03:10 | 03:14 | Mizar 記述 | σ 簡約。属性 `sigma-closed`（8 個の計算規則＋8 個の適合規則＝16 規則）を定義し、`SigmaRed(V)` を「最小の sigma-closed 関係」として定義。最小性（Th33）がそのまま規則帰納法を与える。検証通過。 |
| 03:14 | 03:17 | Mizar 記述 | 算術補題（Th34–Th41）。Mizar の checker が `0 < n` から `1 < n+1` を直接は導かないため `0+1 < n+1` を経由する形に書き換えた。 |
| 03:17 | 03:19 | Mizar 記述 | 長さ減少定理（Th42）: 減少関係が sigma-closed であることを 16 規則すべてについて示し、最小性から `[M,N] in SigmaRed(V) implies elen N < elen M` を得る。続いて停止性を登録 `SigmaRed(V) -> strongly-normalizing`（無限鎖から自然数の無限降下列を作り NAT_1:sch 5（最小原理）で矛盾）。検証通過。 |
| 03:19 | 03:22 | 文書作成 | README.md を作成。全体を `mizf` で再検証し、`text/enveps_1.err` が 0 バイトであることを確認。 |

**成果（`text/enveps_1.miz`、2082 行、定理 43・定義 15・登録 4・スキーム 1、エラー 0）**

- λ_EnvEps の項を DTCONSTR の構文解析木として構成。記号は対で表し、第 1 成分がタグ（0=変数, 1=id, 2=λ, 3=適用, 4=環境拡張, 5=ε, 6=合成）、束縛子は変数で添字付けして junk を出さない設計。
- 構成子の相異・単射性・場合分け・構造帰納法。
- 乗法的長さ測度 `elen` と 7 つの漸化式、正値性。
- σ 簡約を最小の閉包関係として定義（16 規則）。最小性が規則帰納法を与える。
- **σ 簡約は長さを真に減少させる**（Th42）。
- **σ 簡約は停止する**（`SigmaRed(V) is strongly-normalizing`、REWRITE1:def 15）。

**次段階への見通し:** MML の `REWRITE1` には Newman の補題が登録 `cluster strongly-normalizing locally-confluent -> confluent` として既に存在する。したがって σ の局所合流性（臨界対解析）を形式化すれば σ の合流性が自動的に得られる。

### 指示 6

> Aに進んでください

選択肢 A =「λ_EnvEps 経由で λ_FREnv の完全合流性まで」（Isabelle 側で 48 理論規模）。

| 開始 | 終了 | 種別 | 内容 |
|---|---|---|---|
| 09:30 | 09:35 | 環境構築 | 複数記事構成の検証。`miz2prel` でローカル `prel/` を作り、後続記事から `ENVEPS_1` を import できることを確認。`build.sh`（各記事を検証して prel に書き出す）を追加、`prel/` を gitignore。 |
| 09:35 | 09:42 | Mizar 記述 | `enveps_2`: スキーム `RedCong`（1 ステップで閉じた写像は多段簡約でも閉じる）を RedSequence 上の帰納法で証明。これを使って 8 つの適合則の多段版（`SigmaRed(V) reduces M,M1` から `reduces eApp(M,N),eApp(M1,N)` 等）を導出。 |
| 09:42 | 09:47 | Mizar 記述 | `enveps_2`: 反転補題（Th9）。`[P,Q] in SigmaRed(V)` から 16 規則のいずれかの形であることを導く。証明は「16 規則の形をみたす対の集合」が sigma-closed であることを示し最小性を使う（SigmaRed との共通部分を取るのが要点）。 |
| 09:47 | 09:52 | Mizar 記述 | `enveps_2`: 16 規則を 1 ステップ定理として命名（Th10–Th25）。合流の目撃者を与える補助定理（Th26–Th28）。 |
| 09:52 | 09:56 | Mizar 記述 | `enveps_1` に独立変数版の構成子相異定理 Th44 を追加（既存の Th10 は eLam と eExt で同じ変数を共有しており、頭部反転に不十分だった）。 |
| 09:56 | 10:00 | Mizar 記述 | `enveps_3`: 収束の項目撃者（Th1）、頭部構成子ごとの反転補題（Th2–Th8: eVar/eId は簡約不能、eLam/eEps は 1 通り、eApp/eExt は 2 通り、eComp は 10 通り）。続いて適合規則側のピーク補題 6 本（Th9 Lam, Th10 Eps, Th11 AppL, Th12 AppR, Th13 ExtnL, Th14 ExtnR）。 |

**現在の状態（すべて検証済み・エラー 0）**

| 記事 | 行数 | 定理数 | 内容 |
|---|---|---|---|
| `enveps_1` | 2104 | 44 | 構文、構成子、構造帰納法、長さ測度、σ 簡約、長さ減少、停止性 |
| `enveps_2` | 866 | 28 | 多段適合則、反転補題、16 規則の命名、合流補助 |
| `enveps_3` | 1326 | 14 | 頭部別反転、適合規則ピーク 6 本 |

**局所合流性に残るピーク（10 本）**

| ピーク | 反転で生じる場合の数 |
|---|---|
| CompL（合成の左で簡約） | 10 |
| CompR（合成の右で簡約） | 10 |
| Assoc, IdL, IdR, DExtn, VarRef, VarSkip, DApp, EpsEps（8 つの計算規則） | 各 10 |

計およそ 100 の場合分け。各場合は具体的な合流点の構成を要する。これが終われば MML の
`REWRITE1` の登録 `strongly-normalizing locally-confluent -> confluent` により
σ の合流性が自動的に従う。

**A 全体の残り工程**

1. σ の局所合流性（上記 100 ピーク）→ σ の合流性
2. σ 正規形とその文法
3. β 簡約、β|σ 簡約、並行簡約、完全展開
4. 合成適合性、三角性質 → β|σ の合流性 → λ_EnvEps の完全合流性
5. λ_FREnv の構文と βσ 簡約
6. 翻訳・全射性・simulation・多段 lifting → λ_FREnv の完全合流性

### 指示 7

> その進め方でお願いします。

（CompL/CompR から着手し、σ の合流性が出た時点で報告する方針。）

| 開始 | 終了 | 種別 | 内容 |
|---|---|---|---|
| 10:02 | 10:06 | 方針変更 | 規則帰納法ではなく**項の構造帰納法**に切り替え。CompL/CompR ピークを書き始める前に、根規則と適合規則の組合せを数え直したところ、構造帰納法なら入れ子の場合分けが約 100 件から約 30 件に減ることが分かった。すでに書いていた規則帰納法版のピーク補題 6 本（400 行）は不要になるため削除。 |
| 10:06 | 10:10 | Mizar 記述 | `enveps_4`: 収束の対称性（Th1）と、EpsEps 根規則のピーク補題（Th2）。「根規則の簡約結果は、同じ項の任意の簡約結果と合流する」という形に定式化。10 通りの反転を一度書けば、あとは対称性で両向きが得られる。 |
| 10:10 | 10:14 | Mizar 記述 | 根規則ピークの生成器（`gen_root.py`）を作成し、IdL（Th3）と IdR（Th4）を生成。10 通りの反転の定型部分を自動生成し、各ケースの合流構成だけを手で与える方式。 |
| 10:14 | 10:18 | Mizar 記述 | DApp（Th5）。CompL の場合に `eApp` の反転が入れ子になる 2 件を含む。 |
| 10:18 | 10:21 | Mizar 記述 | DExtn（Th6）、VarRef（Th7）、VarSkip（Th8）。 |
| 10:21 | 10:24 | Mizar 記述 | Assoc（Th9）。CompL の場合に `eComp` の反転が入れ子になり 10 件に分岐する最大のケース。文書の臨界対列挙から漏れていた「Assoc 内の DExtn」もここに含まれる。途中、`REWRITE1:15` と `REWRITE1:16` を 1 つの `by` でまとめると checker が「Too many instantiations」で落ちるため、連結補題 `ENVEPS_3:9` を導入して 1 段に短縮した。 |
| 10:24 | 10:25 | Mizar 記述 | 合成の下のピーク（Th10）。W1 が根規則なら Th2–Th9 を直接、W2 が根規則なら対称性経由、両方が適合規則なら帰納法の仮定、という 28 分岐。続いて構造帰納法で**局所合流性**（Th11）を組み立て、登録 `SigmaRed(V) -> locally-confluent` を追加。 |
| 10:25 | 10:26 | 検証 | **σ の合流性**（Th12）が MML の登録 `strongly-normalizing locally-confluent -> confluent` から自動的に導出されることを確認。無証明で通ることが空虚でないことを、偽の命題（`SigmaRed(V) is empty`）が拒否されることで確認した。 |

**到達点（すべて検証済み・エラー 0、計 6289 行）**

| 記事 | 行数 | 定理数 | 内容 |
|---|---|---|---|
| `enveps_1` | 2104 | 44 | 構文、構成子、構造帰納法、長さ測度、σ 簡約、長さ減少、停止性 |
| `enveps_2` | 866 | 28 | 多段適合則、反転補題、16 規則の命名、合流補助 |
| `enveps_3` | 1091 | 9 | 頭部別反転、収束の項目撃者、簡約の連結 |
| `enveps_4` | 2228 | 12 | 8 つの根規則ピーク、合成のピーク、**局所合流性**、**合流性** |

**主定理**

- `ENVEPS_1:43` — `SigmaRed(V) is strongly-normalizing`（σ は停止する）
- `ENVEPS_4:11` — `SigmaRed(V) is locally-confluent`（σ は局所合流）
- `ENVEPS_4:12` — `SigmaRed(V) is confluent`（**σ は合流する**）

**A 全体の残り工程**

1. σ 正規形とその文法
2. β 簡約、β|σ 簡約、並行簡約、完全展開
3. 合成適合性、三角性質 → β|σ の合流性 → λ_EnvEps の完全合流性
4. λ_FREnv の構文と βσ 簡約
5. 翻訳・全射性・simulation・多段 lifting → λ_FREnv の完全合流性

### 指示 8

> 続けてください。

| 開始 | 終了 | 種別 | 内容 |
|---|---|---|---|
| 10:28 | 10:32 | MML 調査 | `REWRITE1` の正規形インフラを確認。登録 `strongly-normalizing -> weakly-normalizing` と `confluent -> with_Church-Rosser_property -> with_NF_property -> with_UN_property` が既にあるため、`SigmaRed(V)` は自動的に `weakly-normalizing` かつ `with_UN_property` になり、正規形関手 `nf(a,R)`（REWRITE1:def 12）とその一意性（REWRITE1:53, 54）がそのまま使えることが分かった。σ 正規形を自前で構成する必要がない。 |
| 10:32 | 10:38 | Mizar 記述 | `enveps_5`: 簡約先が項集合に留まること（Th1）、正規形判定を EnvEpsTerm 上に落とす補題（Th2）、正規形関手 `snf M = nf(M,SigmaRed(V))`（Def1）とその基本則 — 正規形であること・到達可能性（Th3）、一意性（Th4）、正規形は不動（Th5）、簡約は snf を保つ（Th6, Th7）、冪等性（Th8）。 |
| 10:38 | 10:43 | Mizar 記述 | 正規形の文法的特徴づけ。`eVar`/`eId` は正規形（Th9）。`eLam`/`eEps`/`eApp`/`eExt` は部分項が正規形であることと同値（Th10–Th13）。`eComp(M,N)` は「M, N が正規形、N ≠ id、かつ M が eLam または（M が eVar かつ N が eExt でない）」と同値（Th14）。これは Isabelle の文法 (2.32) と同じ内容を、帰納的述語を導入せずに一段の特徴づけとして述べたもの。 |
| 10:43 | 10:45 | Mizar 記述 | 正規形の計算則（Th15–Th19）: `snf(eLam(x,M)) = eLam(x,snf M)`、`snf(eEps M) = eEps(snf M)`、`snf(eApp(M,N)) = eApp(snf M,snf N)`、`snf(eExt(M,x,N)) = eExt(snf M,x,snf N)`、`snf(eComp(M,N)) = snf(eComp(snf M,snf N))`。 |

**到達点（すべて検証済み・エラー 0、計 6924 行）**

| 記事 | 行数 | 定理数 | 内容 |
|---|---|---|---|
| `enveps_1` | 2104 | 44 | 構文、測度、σ 簡約、停止性 |
| `enveps_2` | 866 | 28 | 多段適合則、反転補題、16 規則の命名 |
| `enveps_3` | 1091 | 9 | 頭部別反転、収束の目撃者、連結 |
| `enveps_4` | 2228 | 12 | 8 つの根規則ピーク、合成のピーク、局所合流性、合流性 |
| `enveps_5` | 635 | 19 | σ 正規形、その文法、計算則 |

**A 全体の残り工程**

1. β 簡約（3 つの計算規則＋8 つの適合規則）と β/σ = β ∪ σ
2. β|σ 簡約、並行簡約、完全展開
3. 合成適合性、三角性質 → β|σ の合流性 → λ_EnvEps の完全合流性
4. λ_FREnv の構文と βσ 簡約
5. 翻訳・全射性・simulation・多段 lifting → λ_FREnv の完全合流性

1 は σ で作った生成器がほぼそのまま使える機械的な作業。2〜3 が Isabelle 版でも最大（合成適合性 30KB、三角性質 17KB）で、ここが残りの山になる。

### 指示 9

> 続けてください。

| 開始 | 終了 | 種別 | 内容 |
|---|---|---|---|
| 10:46 | 10:52 | Mizar 記述 | `enveps_6`: β 簡約。属性 `beta-closed`（計算規則 Beta / BetaClos / Comp_ε の 3 本＋適合規則 8 本）、最小の beta-closed 関係 `BetaRed(V)`、所属・最小性・反転（Th3）・11 規則の命名（Th4–Th14）。σ で作った生成器をほぼそのまま流用。 |
| 10:52 | 10:56 | Mizar 記述 | β の多段適合則（Th15–Th22、`ENVEPS_2` の `RedCong` スキームを再利用）と頭部別反転（Th23–Th29）。`eVar`/`eId` は β 簡約不能、`eLam`/`eEps` は 1 通り、`eApp` は 5 通り、`eExt`/`eComp` は 2 通り。 |
| 10:56 | 11:01 | Mizar 記述 | `BetaSigmaRed(V) = BetaRed(V) \/ SigmaRed(V)`（Def3）と所属（Th30）。これが Isabelle の `beta_sigma_step_iff_beta_or_sigma` に対応する。19 規則（β 計算 3 本＋σ 計算 8 本＋適合 8 本、Th31–Th49）と多段適合則（Th50–Th57）。 |

**到達点（すべて検証済み・エラー 0、計 9118 行）**

| 記事 | 行数 | 定理数 | 内容 |
|---|---|---|---|
| `enveps_1` | 2104 | 44 | 構文、測度、σ 簡約、停止性 |
| `enveps_2` | 866 | 28 | 多段適合則、反転、16 規則の命名 |
| `enveps_3` | 1091 | 9 | 頭部別反転、収束の目撃者 |
| `enveps_4` | 2228 | 12 | 根規則ピーク、局所合流性、合流性 |
| `enveps_5` | 635 | 19 | σ 正規形、文法、計算則 |
| `enveps_6` | 2194 | 57 | β 簡約、β/σ 簡約、19 規則 |

**次段階（並行簡約）の設計判断**

Lean 版は完全展開 `bcd` を項上の関数として定義し、三角性質 `PStep M N → PStep N (bcd M)` を経由してダイヤモンド性を得ている。Mizar で同じことをするには問題がある: DTCONSTR の構造再帰（sch 8）は、子の「値」と子の「根記号」しか渡さないため、`app(comp(lam x M, L), N)` のように**孫の構成子**を見る必要がある BetaClos 規則を直接は書けない。

回避策として、完全展開を関数として定義せず、**存在形の三角性質**を構造帰納法で証明する方針を採る:

> 任意の項 M に対し、ある M* が存在して、M からの任意の並行簡約が M* に到達する。

各ケースで M* を帰納法の仮定から構成する。`app` の場合は A の形（ENVEPS_1:17）で場合分けし、A が `lam` のときは帰納法の仮定が与える A* が `lam` 形であることを並行簡約の反転から導いて、必要な部分目撃者を取り出す。これにより `bcd` を Mizar の関手として定義する必要がなくなる。

### 指示 10

> 存在形でお願いします。

| 開始 | 終了 | 種別 | 内容 |
|---|---|---|---|
| 11:03 | 11:16 | Mizar 記述 | `enveps_7`: 並行簡約 `ParRed(V)`。属性 `par-closed`（反射律＋5 つの適合規則＋3 つの並行計算規則の計 9 本）、最小の par-closed 関係、所属・最小性・反転（Th3）・9 規則の命名（Th4–Th12）・頭部別反転（Th13–Th19）。続いて `BetaRed(V) c= ParRed(V)`（Th20）と `[M,N] in ParRed(V)` から `BetaRed(V) reduces M,N`（Th21）。 |
| 11:16 | 11:24 | Mizar 記述 | 述語 `Ms is_par_top_of M`（M からの任意の並行簡約が Ms に到達する）を定義。`[M,Ms] in ParRed(V)`（Th22）と、部分目撃者の取り出し補題 — `eLam`（Th23）、`eEps`（Th24）、`eComp`（Th25）。これが「完全展開を関数として定義しない」方針の要。 |
| 11:24 | 11:35 | Mizar 記述 | 適用の 4 補題。A が冗長でない場合（Th26）、A = eLam の場合（Th27）、A = eEps の場合（Th28）、A = eComp(eLam(..),..) の場合（Th29）。それぞれ 5 通りの並行簡約の反転を処理する。 |
| 11:35 | 11:42 | Mizar 記述 | **三角性質**（Th30）: 任意の項 M に対し `Ms is_par_top_of M` なる Ms が存在する。構造帰納法で証明。`eApp` の場合は A の形（ENVEPS_1:17）で 7 通りに分け、`eComp` の場合はさらに左成分が `eLam` かどうかで分ける。 |
| 11:42 | 11:47 | Mizar 記述 | **ダイヤモンド性**（Th31）と登録 `ParRed(V) -> subcommutative`。MML の登録 `subcommutative -> confluent` により **ParRed の合流性**（Th32）が従う。スキーム `RedSub`（1 ステップが多段に写れば多段も多段に写る）を経て `ParRed reduces` から `BetaRed reduces` へ（Th33）、**β の合流性**（Th34）。 |

**到達点（すべて検証済み・エラー 0）**

| 記事 | 行数 | 定理数 | 内容 |
|---|---|---|---|
| `enveps_1` | 2104 | 44 | 構文、測度、σ 簡約、停止性 |
| `enveps_2` | 866 | 28 | 多段適合則、反転、16 規則の命名 |
| `enveps_3` | 1091 | 9 | 頭部別反転、収束の目撃者 |
| `enveps_4` | 2228 | 12 | 根規則ピーク、局所合流性、σ の合流性 |
| `enveps_5` | 635 | 19 | σ 正規形、文法、計算則 |
| `enveps_6` | 2194 | 57 | β 簡約、β/σ 簡約、19 規則 |
| `enveps_7` | 2651 | 34 | 並行簡約、三角性質、ダイヤモンド性、β の合流性 |

**主定理**

- `ENVEPS_1:43` — σ は停止する
- `ENVEPS_4:12` — σ は合流する
- `ENVEPS_7:30` — 三角性質（任意の項に「すべての並行簡約を吸収する」項が存在）
- `ENVEPS_7:32` — 並行簡約は合流する
- `ENVEPS_7:34` — **β は合流する**

**残り工程**

1. 鍵補題: 並行簡約が σ 正規化と可換（`[P,R] in ParRed` から `[snf P, S] in ParRed` かつ `snf S = snf R` なる S）
2. 1 から β|σ 簡約のダイヤモンド性 → **λ_EnvEps の完全合流性**
3. λ_FREnv の構文と βσ 簡約
4. 翻訳・全射性・simulation・多段 lifting → λ_FREnv の完全合流性

1 が Lean 版 `Compat.lean`（19KB）に対応する残りの山。σ 正規形の文法（`ENVEPS_5:14`）に沿った長さ測度による強帰納法が必要になる。

---

## 2026-09-15 11:27–12:02 形式化（鍵補題）

**指示（逐語）**

> 進めてください

**活動種別**: 形式化・検証

**内容**

`text/enveps_8.miz` に鍵補題までを完成させた。

- Th24–Th28: 合成両立性の eApp ケース（ParRed の 5 通りの逆転に沿って分岐）
- Th29: **合成両立性** — σ 正規形 U, W とそれぞれからの並行簡約 U ⇒ S1, W ⇒ S2 に対し、
  `snf (eComp(U,W))` から並行簡約で、正規形が `snf (eComp(S1,S2))` に一致する項へ到達できる。
  長さ測度 `elen (eComp(U,W))` に関する完全帰納法（`NAT_1:sch 4`）で、σ 正規形の文法
  （`ENVEPS_5:14`）に沿った 9 ケースに分岐。
- Th30: **鍵補題** — `[P,R] in ParRed(V)` ならば
  `ex S st [snf P, S] in ParRed(V) & snf S = snf R`。
  ParRed の最小性（`ENVEPS_7:2`）による規則帰納法で、9 規則すべてを処理する。
  comp ケースで Th29 を使い、betaClos ケースは `snf L = eId V` か否かで場合分けする
  （そうでなければ `eComp(eLam(x, snf M), snf L)` が σ 正規形なので betaClos 冗長式が
  そのまま残り、そうであれば beta 冗長式に潰れる）。

検証済み（`.err` 空）。`enveps_8` は 1461 行、30 定理。

**残り工程**

1. 鍵補題から β|σ 簡約のダイヤモンド性 → **λ_EnvEps の完全合流性**
2. λ_FREnv の構文と βσ 簡約
3. 翻訳・全射性・simulation・多段 lifting → λ_FREnv の完全合流性

---

## 2026-09-15 12:02–12:12 形式化（λ_EnvEps の完全合流性）

**指示（逐語）**

> 進めてください

**活動種別**: 形式化・検証

**内容**

新しい article `text/enveps_9.miz`（421 行、13 定理）で **βσ 簡約の合流性** を証明した。
Hardin の解釈法（interpretation method）をそのまま形式化したもの。

- `SnfPar V`（Def1）— σ 正規形のあいだの関係。`[A,B] in SnfPar V` とは、A が σ 正規形で、
  ある S について `[A,S] in ParRed(V)` かつ `B = snf S` となること。
- Th1 メンバシップ判定、Th2 反射性（σ 正規形上）
- registration `SnfPar V -> subcommutative` — ParRed のダイヤモンド性（`ENVEPS_7:31`）と
  鍵補題（`ENVEPS_8:30`）を合わせると、共通の還元先 `snf W` が取れる。
  MML の `subcommutative -> confluent` クラスタから Th3 `SnfPar V is confluent`。
- Th4–Th8 — σ・β・SnfPar の多段簡約がいずれも βσ 多段簡約に含まれること
  （`ENVEPS_7:sch 1` = RedSub を使用）。Th6 は `M ->>_{βσ} snf M`。
- Th9 — 1 段の βσ 簡約を正規形へ射影: `[M,N] in BetaSigmaRed(V)` なら
  `[snf M, snf N] in SnfPar V`（β 側は鍵補題、σ 側は `snf M = snf N`）。
- Th10 — 多段版（`ENVEPS_8:sch 1` = RedInd を使用）。
- Th11 — 補助: `Relation of TS G` による簡約の到達先は再び項である。
- Th12 — 項の形での合流性。
- Th13 — **`BetaSigmaRed(V) is confluent`**（REWRITE1 の属性としての合流性）。

これで **λ_EnvEps の完全合流性** が Mizar で検証された。

**残り工程**

1. λ_FREnv の構文と βσ 簡約
2. 翻訳・全射性・simulation・多段 lifting → λ_FREnv の完全合流性

---

## 2026-09-15 12:12–12:24 形式化（λ_FREnv の構文と βσ 簡約）

**指示（逐語）**

> 続けてください。

**活動種別**: 形式化・検証

**内容**

λ_FREnv 側の土台を作った。参照実装（`frenv-confluence-WCTP/lean`）の
`docs/frenv-syntax.md` と `LambdaFrenv/Basic.lean` に対応する。

- `text/frenv_1.miz`（819 行、17 定理、8 定義、構造帰納法 scheme 1 つ）—
  λ_FREnv の構文。`enveps_1.miz` の構文部から合成 `eComp` を落として機械的に
  生成した。記号集合は `FrEnvSym(V) = [:{0,2,4},V:] \/ [:{1,3,5},{0}:]`、
  構成子は `fVar / fId / fLam / fApp / fExt / fEps` の 6 個。根記号・相異性・
  単射性・場合分け（Th16）・構造帰納法 `FRENV_1:sch 1` まで。
- `text/frenv_2.miz`（1098 行、25 定理）— βσ 簡約。
  `attr R is bs-closed`（Def1、16 節）、`FrRed(V)`（Def2）、
  Th1 メンバシップ、Th2 最小性、Th3 逆転（16 選言）、
  Th4–Th19 名前つき 16 規則、Th20–Th25 多段合同。

規則は 10 個の根規則（Beta, BetaClos, Stab, Assoc, IdL, IdR, DExt, VarRef,
VarSkip, DApp）と 6 個の合同規則（appL, appR, lam, extL, extR, envAbst）。
λ_EnvEps の `eComp(M,N)` は λ_FREnv では `fApp(fEps M, N)` に対応するので、
λ_EnvEps の β 規則 Comp_ε（`eApp(eEps M,N) -> eComp(M,N)`）は λ_FREnv では
恒等ステップになる。これが「翻訳は各ステップを 0 歩または 1 歩で模倣する」
という Lean 版の注記に対応する。

なお本形式化では両計算系とも定数（`Const`）を持たない。Lean 版は定数と規則
`ε(c)M -> c` を持つが、これは `ε(ε(M))N -> ε(M)`（Stab）と同型の扱いであり、
合流性の議論には本質的に効かない。

**残り工程**

1. 翻訳 `tr : λ_EnvEps -> λ_FREnv`・全射性・simulation・多段 lifting
   → λ_FREnv の完全合流性

---

## 2026-09-15 12:24–12:43 形式化（翻訳と λ_FREnv の完全合流性）

**指示（逐語）**

> 続けてください。

**活動種別**: 形式化・検証

**内容**

翻訳 `tr : λ_EnvEps -> λ_FREnv` を定義し、λ_FREnv の合流性まで到達した。
参照実装 `frenv-confluence-WCTP/lean/LambdaFrenv/Translation.lean` に対応する。

- `text/frenv_3.miz`（799 行、20 定理）— 翻訳。
  `TrF(V)`（Def4）を `DTCONSTR:sch 8` による構造再帰で定義し、`tr M`（Def5）。
  再帰の値を取り出すための選択子 `fsel / vsel / fseq`（`natsel` と同じ手口）。
  Th8–Th13 が 7 つの再帰等式で、要は `tr (eComp(M,N)) = fApp(fEps (tr M), tr N)`、
  他の構成子は同名の構成子に移る。Th14 全射性（λ_FREnv の構造帰納法）。
  Th15–Th20 翻訳の逆転（`tr M = fApp(a,b)` は eApp 由来か eComp 由来）。
- `text/frenv_4.miz`（473 行、3 定理）— **simulation**。
  関係 `Q = { [A,B] : FrRed(V) reduces tr A, tr B }` が beta-closed かつ
  sigma-closed であることを示し、最小性から `BetaSigmaRed(V) c= Q`。
  Th2 が 1 歩、Th3 が多歩。β 規則 Comp_ε は 0 歩に写る。
- `text/frenv_5.miz`（879 行、8 定理）— **lifting と合流性**。
  - Th1/Th2 `eEps` 頭の βσ 簡約の逆転（多歩版）
  - Th3 `tr M = fApp(fEps X, Y)` の原像: `M ->>_{βσ} eComp(A,B)` で
    `tr A = X`, `tr B = Y`
  - Th4 **1 歩 lifting** — `[P,Q] in FrRed(V)` かつ `tr M = P` ならば、
    `tr N = Q` なる N と共通の簡約先 L が取れる。FrRed の最小性による
    規則帰納法、16 節。DApp の節と appL の節では原像が eComp の場合に
    ずれが生じ、そこで「共通簡約先 L」という形が効く。
  - Th5 **多歩 lifting** — λ_EnvEps の合流性（`ENVEPS_9:12`）で
    各段の証人を突き合わせる。
  - Th6 項の形での合流性、Th8 **`FrRed(V) is confluent`**。

これで **λ_FREnv の完全合流性** が Mizar で検証された。
`./build.sh enveps_1 .. frenv_5` で 14 article すべてを再検証済み。

**主定理**

- `ENVEPS_1:43` — σ は停止する
- `ENVEPS_4:12` — σ は合流する
- `ENVEPS_7:34` — β は合流する
- `ENVEPS_8:30` — 並行簡約は σ 正規化と可換（鍵補題）
- `ENVEPS_9:13` — λ_EnvEps の βσ は合流する
- `FRENV_5:8` — **λ_FREnv の βσ は合流する**

---

## 2026-09-15 16:55–18:20 可読性のための全面改訂

**指示（逐語）**

> Mizarのコードをよんでみましたが、Mizarでの形式化は、項の定義など、再帰的定義がないため、すごく読みにくいです。
> 可読性を向上させる方法はないですか？

> (2)まで含めて一気にお願いします。

> β/βσ層を先に片付けてください

> 停止性と下流の付け替えに進んでください

**活動種別**: 設計変更・形式化・検証

**内容**

読みにくさの原因を 3 つに切り分け、すべてに対処した。

1. **再帰的定義がない** — `elen` と `tr` が `DTCONSTR:sch 8` を直に叩いており、
   選択子 `natsel`/`fseq` と `IFEQ` の 4 段ネストが露出していた。
2. **規則テキストの重複** — 帰納的述語がないため、各規則が「属性の節・存在性の
   登録・coherence の登録・反転補題の選言・命名定理」の 5 箇所に書かれていた。
   合同規則 appL の本文は開発全体で 25 回出現していた。
3. **構文解析木の層が漏れていた** — `Relation of TS(EnvEpsGram(V))` を使うため、
   後続の記事にも `R c= [:TS G,TS G:]; then ...; then reconsider ...` の
   5 行定型が数十箇所に現れていた。

**新しい基盤（3 記事）**

- `envsyn`（1258 行、26 定理）— 構文解析木の層をここに閉じ込め、**構造再帰
  スキーム** `ENVSYN:sch 2` を `DTCONSTR:sch 8` から一度だけ証明した。
  選択子と `IFEQ` 連鎖はスキームの内側にある。あわせて `EnvEpsRel` モードと
  対の取り出し補題（原因 3 の定型を引用 1 個に潰す）、構成子の中置記法。
- `envlen`（388 行、15 定理）— 長さ測度。定義が 7 本の等式になった。
- `envcc`（1709 行、30 定理）— 任意の関係 `Q` の**合同閉包** `CC Q`。
  8 つの合同規則・反転・頭部別反転 7 本・多段合同則 8 本・単調性・
  `CC (Q1 \/ Q2) = CC Q1 \/ CC Q2` を、計算系ごとではなく一度だけ証明する。

**計算系（2 記事）**

- `envsig`（1601 行、56 定理）— σ の根規則 8 本を明示的な関係として書き、
  `SigmaRed(V) = CC SigmaRoot(V)`。16 の命名規則・反転・頭部別反転・多段合同は
  すべて `envcc` からの数行の導出。長さ減少と停止性も移植した。
- `envbeta`（1217 行、61 定理）— β の根規則 3 本、`BetaRed(V) = CC BetaRoot(V)`、
  `BetaSigmaRed(V) = CC BetaSigmaRoot(V)`。
  `BetaSigmaRed(V) = BetaRed(V) \/ SigmaRed(V)` は定義ではなく**定理**
  （`ENVBETA:32`）になり、一般則 `CC (Q1 \/ Q2) = CC Q1 \/ CC Q2` から従う。

**下流の付け替え**

旧 `enveps_1, 2, 3, 6` を退役させ、残りを内容に即した名前に改めた
（`enveps_4 → envpeak`, `enveps_5 → envnf`, `enveps_7 → envpar`,
`enveps_8 → envkey`, `enveps_9 → envconf`）。引用の付け替えは
定理番号の対応表をスクリプトで当て、検証器に照合させた。
構造の書き換えが必要だったのは 2 箇所だけ。

- `envpar` の Th20（`BetaRed(V) c= ParRed(V)`）— `ParRed(V) is beta-closed`
  を `ParRed(V) is_cc_over BetaRoot(V)` に。
- `frenv_4` の Th2（simulation）— 旧版は `Q1 is beta-closed`（11 節）と
  `Q1 is sigma-closed`（16 節）を別々に証明していた。新版は
  `Q1 is_cc_over BetaSigmaRoot(V)` 一本で済み、8 つの合同節が 1 回になった。

**到達点**

15 記事、17,659 行、369 定理。`./build.sh` で全記事が検証を通る。
主定理は `ENVSIG:51`（σ の停止性）、`ENVPEAK:12`（σ の合流性）、
`ENVPAR:34`（β の合流性）、`ENVKEY:30`（鍵補題）、
`ENVCONF:13`（λ_EnvEps の合流性）、`FRENV_5:8`（λ_FREnv の合流性）。

行数の合計はほぼ変わっていない（17,717 → 17,659）。置き換えた 4 記事
（6,255 行）と新しい 5 記事（6,173 行）もほぼ同じである。削減されたのは
行数ではなく**重複**で、各計算系の規則は 1 回しか書かれておらず、
合同閉包まわりの一般論は 3 つの簡約関係で共有されている。
