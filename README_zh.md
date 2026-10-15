[English](README.md) | [简体中文](README_zh.md)

# Lean 4 中欧拉函数的大纤维（Erdős 问题 821）

对每个 ε > 0，都有无穷多个 n，使得方程 φ(m) = n 的解 m 多于 n^(1-ε) 个。这解决了关于欧拉函数最大纤维的Erdős 猜想（[Erdős 问题 #821](https://www.erdosproblems.com/821)）；其形式为 Formal Conjectures 的 `erdos_821`，答案为 `True`。

- **作者：** Yao Xu ([@cadamcat](https://github.com/cadamcat))；见[作者与署名说明](AUTHORS.md)。
- **数学结果：** OpenAI，[*Weighted dilation graphs, smooth shifted primes and totient fibers*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/paper.pdf)，定理 1.1，由定理 1.2（光滑移位素数）推出。
- 本项目在 AI 协助下开发；所有证明均由 Lean 4 内核验证。

## 主要结果

```lean
namespace Erdos821

/-- The number of `m` with `φ(m) = n`. -/
noncomputable def g (n : ℕ) : ℕ :=
  {m : ℕ | Nat.totient m = n}.ncard

theorem erdos_821 :
    ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite
```

该定理位于 [Erdos821/Theorem.lean](Erdos821/Theorem.lean)；[Challenge.lean](Challenge.lean) 只用 Mathlib 词汇表述该定理，而 [Challenge.json](Challenge.json) 配置 [Comparator](https://github.com/leanprover/comparator) 来比较二者。证明使用的定义 `g` 和 `Statement` 位于 [Erdos821/Challenge.lean](Erdos821/Challenge.lean)。

### 与 Formal Conjectures 的关系

Formal Conjectures 将 `erdos_821 : answer(sorry) ↔ ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite` 表述为猜想（`FormalConjectures/ErdosProblems/821.lean`，提交 `317647fa3fc24ae900a50382186da1d22e4ea398`）。这里的定理是其右端，因此证明了答案为 `True` 的陈述。逐项对照如下：

| 条款 | Formal Conjectures | 本项目 |
| --- | --- | --- |
| 纤维计数 | `{m : ℕ \| totient m = n}.ncard`（使用 `open Nat`） | `{m : ℕ \| Nat.totient m = n}.ncard`，相同的项 |
| 量词 | `∀ ε > (0 : ℝ)` | 相同 |
| 比较关系 | `(g n : ℝ) > (n : ℝ) ^ (1 - ε)`，实数幂 | 相同 |
| 结论 | `Set.Infinite` | 相同 |
| 答案 | `answer(sorry)` | `True` |

二者都计入 `m = 0` 和 `n = 0`。由于 `φ 0 = 0`，`m = 0` 只属于 `n = 0` 的纤维，因此 `g 0 = 1`；一个 `n` 的取值不可能改变该集合是否为无限集。每个纤维都是有限集，所以 `ncard` 给出的是真正的计数。[Erdos821/Fidelity/FormalConjectures.lean](Erdos821/Fidelity/FormalConjectures.lean) 逐字复制 Formal Conjectures 的定义，并证明目标等价于 `answer(True)` 时的 `erdos_821`，也等价于论文的定理 1.1；论文只计数 `m ≥ 1` 且 `n ≥ 1` 的情形。

## 构建与验证

环境要求：Git、Python 3 和 [elan](https://github.com/leanprover/elan)，并确保 `lake` 在 `PATH` 中。在仓库根目录运行：

```sh
lake update
scripts/apply-oai-patches.sh
lake exe cache get
lake build
```

OpenAI 的 `lake update` hook 可能在解析完依赖并写入 `lake-manifest.json` 后退出并报错，错误以 `iut: Lake resolved an unexpected checkout at …` 开头。接着运行补丁脚本：它会将 OpenAI 的 Lean 4.34.1 兼容性补丁应用到已获取的软件包上；再次运行 `lake update` 后也可以重新运行该脚本。

然后运行：

```sh
./scripts/verify.sh
```

该脚本会构建库、挑战陈述和 [Verification](Verification)，检查经 `pp.all` 打印的 `Erdos821.erdos_821` 的展开陈述及定义 `g` 是否与 `Challenge.lean` 一致；扫描所有 Lean 源文件中的 `sorry`、`admit`、新增公理、`native_decide`、`implemented_by`、`extern` 和不安全代码；并要求 `Erdos821.erdos_821` 恰好依赖 `propext`、`Classical.choice` 和 `Quot.sound`。所有检查通过时退出状态码为 0；证明仍依赖 `sorry` 时退出状态码为 2；其他失败则退出状态码为 1。全新克隆后构建 v1.0.0、其公理检查、内核重放和 Comparator 的记录结果见 [docs/verification.md](docs/verification.md)。

[Verification/NonVacuity.lean](Verification/NonVacuity.lean) 检查该谓词在具体取值上并非平凡（`g 4 = 4 > 4^(1/2)`，而 `g 3 = 0`），每个纤维都是有限集，并且 Formal Conjectures 的陈述及论文定理 1.1 都可由该定理推出；内核求值示例见 [Erdos821/Fidelity/Examples.lean](Erdos821/Fidelity/Examples.lean)。目标是一个没有假设的封闭命题，因此无需再实例化其他内容。

## 证明结构

形式化证明遵循论文。[Erdos821/Supply.lean](Erdos821/Supply.lean) 陈述定理 1.2：对每个 `0 < δ < 1/4` 和 `σ > 0`，当 `x` 足够大时，至少有 `x^(1-σ)` 个素数 `p` 满足 `2x < p ≤ 5x`，且 `p - 1` 的每个素因子都不超过 `x^δ`。[Erdos821/Assembly.lean](Erdos821/Assembly.lean) 由此推出Erdős 问题 821（论文第 8 节），并使用 OpenAI 给出的有限纤维上界。[Erdos821/Blueprint/](Erdos821/Blueprint) 为定理 1.2 的证明固定了十个工作包接口 P1–P10；[Erdos821/Final/Assembly.lean](Erdos821/Final/Assembly.lean) 将各工作包的证明组装为 `Erdos821.Final.statement`。

`Blueprint` 各模块将每个工作包接口表述为命题（`X_statement`）；各工作包通过定理证明该命题，`Erdos821.Final.packageInterfaces` 则汇集这些证明。仓库中唯一的 `sorry` 位于 `Challenge.lean`，Comparator 要求保留该占位符。

| 工作包 | 论文 | 接口 |
| --- | --- | --- |
| P1 | §2 初步估计：素数估计、调和特征、因子矩、均值、导数检验、傅里叶分离 | `classical_inputs` |
| P2 | §2 分块筛法 | `sieve_inputs` |
| P3 | §3 膨胀图的迁移原理 | `transference_inputs` |
| P4 | §4 小理想核 | `ideal_inputs` |
| P5 | §5 提升后的移位相关性 | `shifted_cancellation` |
| P6 | §6 Type II 估计 | `typeII_estimate` |
| P7 | §7 候选几何、界与 Type I 估计 | `candidate_geometry`、`candidate_bounds`、`candidate_typeI` |
| P8 | §7 代理量与密度 | `proxy_inputs` |
| P9 | §7 平衡粗数界 | `balanced_rough_bound` |
| P10 | §7 素数提取与素数计数 | `prime_extraction`、`count_from_weighted_mass` |

该库有 939 个模块。目录按工作包命名（`P<k>…`），或保留较早的章节标签（P3 对应 `S2…`，P4 对应 `S34…`，P6 对应 `S56…`，P9 对应 `S9…`，P10 对应 `S10…`）：

| 工作包 | 目录（模块数） |
| --- | --- |
| P1 | `Classical/` (5), `P1/` (4) |
| P2 | `P2Rough/` (1), `Prelim/` (17) |
| P3 | `P3/` (2), `P3Adj/` (7), `P3Birth/` (1), `P3Clean/` (60), `P3Edge/` (28), `P3Final/` (1), `P3GW/` (1), `P3High/` (11), `P3Live/` (3), `P3LowRank/` (4), `P3Mark/` (1), `P3Pair/` (1), `P3Phys/` (1), `P3Rare/` (3), `P3Restore/` (3), `P3Rows/` (1), `P3Span/` (1), `P3Sum/` (1), `P3Tail/` (2), `S2/` (88), `S2Contr/` (1), `S2Empty/` (12), `S2Full/` (1), `S2Gpar/` (1), `S2High/` (10), `S2Hist/` (1), `S2Ltrans/` (1), `S2Nondiv/` (1), `S2Packet/` (1), `S2Phys/` (1), `S2Resid/` (1), `S2Root/` (2), `S2Tail/` (1) |
| P4 | `P4Bridge/` (11), `P4Cancel/` (4), `P4Cell/` (1), `P4Char/` (1), `P4Count/` (1), `P4Frame/` (1), `P4Independent/` (1), `P4Marg/` (1), `P4Probe/` (43), `P4Proj/` (1), `P4Rat/` (2), `P4Shared/` (1), `S34/` (58) |
| P5 | `P5/` (170), `P5CellCost/` (1), `P5Div/` (1), `P5Energy/` (6), `P5FourierArcProof/` (1), `P5Gram/` (2), `P5Log/` (1), `P5MarkedEnergy/` (26), `P5Mellin/` (3), `P5Minor/` (1), `P5MinorAdapter/` (2), `P5SmoothSquare/` (1) |
| P6 | `P6Cut/` (1), `P6Maj/` (1), `P6Mass/` (1), `P6Off/` (55), `P6Reidx/` (1), `P6Slot/` (1), `P6Split/` (1), `P6Sq/` (2), `P6Sum/` (1), `S56/` (72) |
| P7 | `P7/` (28), `P7Band/` (3), `P7Char/` (11), `P7Free/` (2), `P7HQ/` (1), `P7Place/` (1), `P7Prefix/` (1), `P7TypeI/` (1), `P7Win/` (1) |
| P8 | `P8/` (35), `P8Grid/` (4), `P8Int/` (1), `P8Low/` (1), `P8Np/` (1), `P8Res/` (1), `P8Tail/` (1) |
| P9 | `P9/` (20), `S9/` (13), `S9Budget/` (1), `S9Div/` (1), `S9Mask/` (3), `S9Norm/` (1) |
| P10 | `Count/` (1), `P10/` (2), `S10/` (5), `S10Bfac/` (1), `S10Brough/` (1), `S10Cover/` (1), `S10Prime/` (2), `S10Sharp/` (2) |
| 陈述、接口、组装、共享引理 | `Assembly.lean` (1), `Blueprint/` (18), `Challenge.lean` (1), `Fidelity/` (2), `Final/` (1), `Leaves/` (7), `Leaves.lean` (1), `Prelim.lean` (1), `Supply.lean` (1), `Theorem.lean` (1) |

## 固定依赖

- Lean `v4.34.1`，由 [lean-toolchain](lean-toolchain) 选定。
- [Mathlib](https://github.com/leanprover-community/mathlib4)，提交 `d13f23b723b8a846827a245b89c10fc7d3f11612`。
- OpenAI 的 [`openai/math`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean)，提交 `adc7f1241b42e322a6451854ab7e4b4c146bf78a`。
- OpenAI 库固定的其余依赖版本，均列于 [lake-manifest.json](lake-manifest.json)。

## 数学参考文献

- OpenAI，[*Weighted dilation graphs, smooth shifted primes and totient fibers*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/paper.pdf)，2026 年 9 月 24 日。
- [Erdős 问题 #821](https://www.erdosproblems.com/821)。
- C. Pomerance，*Popular values of Euler's function*，Mathematika 27（1980），84–89。该文将猜想表述为：对无穷多次成立的 `g(n) > n^c` 中，指数 `c` 的上确界 `C` 满足 `C = 1`。

## 许可证

Apache-2.0；见 [LICENSE](LICENSE)、[NOTICE](NOTICE) 和 [THIRD_PARTY.md](THIRD_PARTY.md)。
