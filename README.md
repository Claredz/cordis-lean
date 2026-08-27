# Cordis Lean — Paper Formalization and Audit

本仓库使用 Lean 4 对 Cordis 论文 *A Programming Paradigm for Spatiotemporal Composability* 进行形式化重建、数学审计，并为后续的论文模型 ↔ Cordis runtime refinement 建立基础。

> 当前主线不是对旧简化生命周期模型继续扩展，也不是把论文公式逐字翻译成 Lean。目标是区分并连接：**论文原始陈述、必要的数学修复、Lean 中可验证的语义模型，以及真实 Cordis 工程实现**。

## 当前状态

仓库正在从早期的简化 Cordis 机制化模型迁移到新的 paper-first formalization。

当前新的权威材料位于 `Cordis-new/`：

- `DeepSeek-Harness-01-Formal-Reference.md` — 论文形式化参考与符号解释。
- `blueprint/DeepSeek-Harness-03-Definition-Theorem-Dependency-Graph.md` — 74 个编号 formal items 与 8 个辅助 formal blocks 的冻结依赖基线。
- `blueprint/DeepSeek-Harness-04-Formalization-Disposition-Specification.md` — 对每个 formal item 的 DIRECT / REPAIR / SUBSUMED / EXPOSITORY / DEFER 分类与审计结论。
- `blueprint/architecture-decision/` — 已接受或正在收敛的架构决策与 Lean spikes。

截至 2026-08-26，已形成以下主要 ADR：

1. **ADR-01 — Equivalence Architecture**：raw exact algebra + 显式 relation-parametric law layer。
2. **ADR-02 — Coeffect Store / Specification / Partiality**：`Finmap` dependent store，`Set`/`Finset` 双层 specification，显式 partial semantics。
3. **ADR-03 — Unified State / Registry**：以正递归的有限 registry shell 替代论文 D32 的字面递归 fixed-point 方程。
4. **ADR-04 — Incarnation Identity / Alpha-Equivariance**：区分 runtime atom 与一次 allocation lifetime 的 `IncarnationId`，为 trace、freshness 与 alpha-renaming 建立接口。

论文审计已经记录多项高影响问题，包括 D8 witness packaging、D25/D26 computability、L35 returned-inverse coherence、D32 negative recursion、fiber-name reuse、L68 support-cycle outline、T66 trace scope 等。它们应被机械化验证或修复，而不是在 Lean 中静默绕过。

## 研究结构

项目采用下面的概念分层：

```text
historical Cordis engineering
          ↓ abstraction
paper semantics
          ↓ audit / repair
Lean formal model
          ↓ refinement / simulation
Cordis runtime
```

计划中的正式代码层次是：

```text
Cordis/Paper/        -- 论文定义、定理及明确标注的 repaired statements
Cordis/Runtime/      -- 对官方 Cordis runtime 的抽象 operational model
Cordis/Refinement/   -- Paper ↔ Runtime 的 simulation / refinement results
Cordis/Audit/        -- counterexamples、no-go results、scope/computability audits
```

这些 production modules 尚在从 architecture spikes 迁移中。当前不要把 `Cordis-new/.../*Spike.lean` 当成最终 API。

## 旧形式化模型

根目录现有的：

```text
Cordis/Core
Cordis/Effects
Cordis/Integrated
Cordis/Extended
Cordis/Examples
```

以及 `PLAN.md`、`PAPER_MAP.md`、`LAYERS.md`、`ASSUMPTIONS.md`、`CONFLUENCE_STATUS.md` 等相关文档，属于 **legacy simplified model**。

该模型已经包含 preservation、withdrawal safety、termination、quiet reachability、Core confluence、provider replacement 等有价值的机械化结果，但它明确不是对当前论文的逐项形式化，也不是 Cordis TypeScript runtime verification。它现在只作为历史成果、反例来源和设计参考保留，不再作为新主线的语义权威。

冻结快照见：

- branch `archive/legacy-formalization-2026-08-24`
- commit `afa8a0e29513c8be34878e054fa18f36def5fa6f`

详细迁移说明见 [`ARCHIVE.md`](./ARCHIVE.md)。

## 分支策略

- **`main`** — 当前正式主线；应始终代表最新被接受的 paper-formalization 架构与 production work。
- **`new-paper-formalization`** — 迁移期间的 staging branch；本轮整理后不应再与 `main` 独立演化，待协作者全部切换后可删除。
- **`archive/legacy-formalization-2026-08-24`** — 旧简化模型的冻结归档，不再开发。
- **`codex/initial-upload`** — 历史分支，目前与旧归档快照指向同一提交，视为 deprecated。

新功能原则上从 `main` 开独立 topic branch，再通过 PR 合回 `main`。

## 形式化原则

1. **Paper statement 与 repaired statement 必须区分。** 不能为了让 Lean 接受而静默改变论文命题。
2. **假命题优先机械化反例。** 不通过强化 `WellFormed`、加入不可能假设或退化 relation 来“证明”。
3. **runtime guarantee 与 paper hypothesis 必须区分。** 例如 effect commutation、inverse correctness、total provision 等不能假装是 TypeScript runtime 自动检查的性质。
4. **优先复用 mathlib。** 有限 dependent map、relation closure、well-foundedness、cardinal、permutation/equivariance 等应先审计现有 API。
5. Lean source 不允许 `sorry`、`admit` 或项目自定义不受控 `axiom` 作为交付结果。

仓库级开发规范见 [`AGENTS.md`](./AGENTS.md)。

## 工具链

项目当前固定使用 Lean/mathlib `v4.33.0`：

```toml
[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.33.0"
```

旧 `Cordis` library 目前仍保留为 regression/reference build target。新的 production modules 建立后，会再单独调整 Lake default target；本轮仓库整理不通过删除旧 target 来制造一个无法构建的“干净目录”。

## 下一阶段

近期工作优先级：

1. 将 ADR-01/02 已稳定的 Effects 与 flat Coeffects 从 spike 迁移为 production Lean modules，并纳入 `lake build`。
2. 机械化高价值 audit targets，例如 D8、D25/D26、D32 与 L68。
3. 继续解决 iterator、staging、control 与 support 的架构 blocker，再进入 Section 4 metatheory 的完整重建。
4. 在 paper model 稳定后建立官方 Cordis runtime abstraction 与 refinement layer。
