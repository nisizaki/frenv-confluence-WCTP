# FREnv 的合流性 — WCTP 2026 验证材料

[English](README.md) | [日本語](README-ja.md) | [Tagalog](README-tl.md) | 简体中文

本仓库收录了使用 Isabelle/HOL 形式化的 FREnv 完整 β/σ 归约关系的合流性证明，以及相关的 Lean 4 形式化开发。本仓库旨在作为提交至 WCTP 2026 的论文的配套验证材料。

**验证结果：** 2026 年 9 月 13 日，Isabelle2025-2 的构建与 Lean 4.33.0 的构建及审计均在干净的 GitHub Actions 运行器上、于包含 Lean 合流性证明的提交 `52881ab` 上通过。所验证的准确提交版本及日志见[验证记录](docs/verification.md)。

**两项形式化开发现均已各自独立证明了完整的合流性。** Isabelle 包含完整归约关系的合流性定理及其依赖项。Lean 开发亦针对自身的编码证明了同一命题，即 `LambdaFrenv.frenv_beta_sigma_confluent`，所采用的证明路线相同（辅助演算、σ 正规化、σ 上的 β、翻译），但定义与证明均为 Lean 自身的。两种编码仍有差异——Lean 具有原始常量类型——本验证材料并不声称二者的等价性已获证明。

## 目录结构

```text
isabelle/
  ROOTS                 注册源文件齐备的四个会话
  FREnv/                FREnv 的语法、归约及局部合流性
  EnvEps/               辅助演算及完整归约关系的合流性转移
  vendor/               所需的 AFP Regular-Sets 和 Abstract-Rewriting 源码
  docs/                 英文数学说明
  README.md             Isabelle 构建及交互式检查说明
lean/
  lean-toolchain        固定的 Lean 版本
  lakefile.toml         Lake 项目配置
  lake-manifest.json    依赖清单（无外部软件包）
  LambdaFrenv.lean       库入口文件
  LambdaFrenv/          定义与证明，含合流性定理
  LambdaFrenv/EnvEps/   辅助演算及其合流性证明
  Audit.lean            检查声明并输出定理所依赖的公理
  docs/                 语法与归约关系的英文规范
  README.md             Lean 构建说明、模块结构及证明路线
docs/
  proof-map.md          主要结果、依赖路径及两项开发的差异
  verification.md       验证记录
UPSTREAM.json           原始源码的准确提交版本及原始文件哈希
PROVENANCE.md           提取范围及整理验证材料时的修改
.github/workflows/      独立的 Isabelle 和 Lean 验证任务
```

## 获取验证材料

```sh
git clone https://github.com/nisizaki/frenv-confluence-WCTP.git
cd frenv-confluence-WCTP
git rev-parse HEAD
```

引用或评估本验证材料时，请记录完整的提交哈希。使用 `git checkout <commit-hash>` 可复现指定版本。构建当前检出的版本不需要子模块，也不需要另行获取原始仓库。

## 使用 Isabelle/HOL 验证

从[官方安装页面](https://isabelle.in.tum.de/installation.html)安装适用于您所用平台的 **Isabelle2025-2**。将其 `bin` 目录加入 `PATH`，然后在本仓库的根目录下运行：

```sh
isabelle version
isabelle build -v -j 1 -o threads=2 -o quick_and_dirty=false -D isabelle
```

此命令将构建随仓库提供的 AFP 依赖库、`FREnv` 会话，以及包含以下最终结果的 `EnvEps` 会话：

```text
FREnv_Full_Confluence_Via_Translation.frenv_beta_sigma_confluent
```

该结果表明：从同一个 FREnv 项出发的任意两条有限 β/σ 归约序列，其终点都可归约到某个共同的项。有关各平台的详细说明及交互式检查方法，请参阅 [Isabelle 使用说明](isabelle/README.md)。证明检查已启用：本验证材料显式禁用了 `quick_and_dirty`。

## 使用 Lean 4 验证

安装 Lean 工具链管理器 [Elan](https://lean-lang.org/install/manual/)，并确保可以通过 `PATH` 运行 `lake`。然后执行：

```sh
cd lean
lake env lean --version
lake build
lake env lean Audit.lean
```

仓库中的 `lean-toolchain` 指定了 **leanprover/lean4:v4.33.0**。Elan 会在需要时下载该版本。本项目不依赖 Mathlib，也不需要下载缓存。本次构建确立了

```text
LambdaFrenv.frenv_beta_sigma_confluent
```

即 Isabelle 中该定理在 Lean 中的对应结果。关于模块结构与证明路线，请参阅 [Lean 使用说明](lean/README.md)。

## 结果与范围

| 形式化开发 | 主要验证内容 | FREnv 完整归约关系的合流性 |
|---|---|---|
| Isabelle/HOL | 辅助演算的合流性、翻译、满射性、模拟、提升以及最终合流性定理 | 已通过记录中的严格会话构建验证 |
| Lean 4 | 抽象重写与 Newman 引理、辅助演算、σ 的停机性与合流性、σ 正规形、并行 β 的菱形性质、复合相容性、翻译与提升 | 已通过记录中的 Lean 构建验证 |

两项开发所使用的语言也有差异：Isabelle 使用字符串表示名称，且没有原始常量；Lean 使用类型来参数化变量和常量。本验证材料并不声称这两种编码的等价性已经得到证明。[证明路线图](docs/proof-map.md)说明了这些差异。

数学说明 Markdown 文件解释了证明路线，但这些文字本身并未经过机器检查。为便于追溯，保留了对原学位论文及路线图的引用；运行任一证明助理均不需要学位论文的 PDF。

## 可复现性与署名

固定的上游版本及整理验证材料时所作的修改见 [PROVENANCE.md](PROVENANCE.md)，各文件的源码来源清单见 [UPSTREAM.json](UPSTREAM.json)，实际验证结果见 [docs/verification.md](docs/verification.md)。两个 GitHub Actions 任务会在干净的运行器上重复执行构建命令。

随仓库提供的 AFP 源码保留了作者及许可证声明，详见[依赖库声明](isabelle/vendor/README.md)。此次提取并未为上游形式化开发赋予新的统一许可证。
