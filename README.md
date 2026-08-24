# Cordis Lean 机制化项目

本项目形式化了 **Cordis** 的部分核心思想。Cordis 源于 **DeepSeek
Harness** 的运行时架构研究，用于在显式依赖和生命周期规则下组合、管理和
替换运行时组件。设计背景见随附的
[Cordis 论文](https://github.com/cordiverse/paper/blob/main/paper.pdf)。

Cordis 的基本思路是把应用表示成一组具有独立身份的 *fiber*。一个 fiber
可以向其他 fiber 提供能力，也可以通过依赖 key 消费能力，并按照受控的
生命周期推进。Cordis 将稳定配置中的依赖观察与进行中的生命周期转换区分
开来，使 provider 可以被安装、激活、转移、卸载或替换，而不要求每个
consumer 直接处理整个运行时的状态。

本 Lean 项目研究的是这一思想的数学核心。它是一个**简化的机制化模型**，
不是对完整 Cordis 论文、DeepSeek Harness 或生产实现的验证。

## Cordis 架构概览

在模型中，catalog 描述 fiber、provider 能提供的能力 key 以及 consumer
依赖的 key。Provider resolution 为每个依赖 key 选择唯一的 active provider。
Consumer 保留当前稳定配置中的 committed view；生命周期转换则准备下一个
稳定配置的 target view。

```text
declared catalog and dependencies
              │
              ▼
    provider resolution ─────► target dependency view
              │                         │
              ▼                         ▼
      lifecycle normalization ─► committed dependency view
              │
              ├──── reversible effects and rollback
              │
              └──── quiet state ─► retire / remove / insert / normalize
```

Committed view 与 target view 的区分非常重要：正在 unloading 的 provider 仍然
可能处于 installed 状态，因此可以继续出现在 consumer 的 committed view 中；
而新选中的 target provider 必须已经 active。当不再有生命周期工作时，状态
被称为 *quiet*。Registry mutation 和 provider replacement 被建模为显式的
有限 epoch，并且结构性操作只能发生在 quiet 边界。

论文中的运行时架构更丰富，还涉及 iterator 驱动的 effects、异步工作、失败
处理、realms、动态 child registration 以及实现层行为。这些内容没有被
悄悄扩展进下面的 Lean 模型。

## 本项目的机制化内容

形式化代码遵循严格的分层依赖关系：

```text
Core → Effects → Integrated → Extended → Examples
```

1. `Cordis.Core` — 有限生命周期与依赖演算、provider resolution、安全性、
   progress、反向优先级终止度量、quiet 状态可达性，以及经过检查的反例。
2. `Cordis.Effects` — 带 witness 的独立可逆 effects、LIFO 逆操作累积、有限
   program、前缀 rollback 和 independence predicates。
3. `Cordis.Integrated` — 携带有限 effect program 的生命周期阶段、到 Core 的
   erasure、精确 rollback、交错的选择性 erasure，以及结合 Core 度量与剩余
   program 长度的字典序终止证明和 integrated quiet-state reachability。
4. `Cordis.Extended` — 机械构造的独立 residual steps、对 Priority 相关 peak
   的穷尽 join、有效状态上的完整 Core confluence、唯一 quiet normal form、
   项目内的 Newman 引理，以及显式的 quiet-only 有限 provider replacement
   epochs。
5. `Cordis.Examples` — 具体的 chain/diamond schedules、quiet-state 证明、可执行
   effect 测试、经过检查的五阶段 replacement derivation，以及具体的
   `Agent → Model → APIProvider` 替换。

目前已检查的较强结果包括：WellFormed preservation、在显式
priority-acyclicity 假设下的无死锁性、生命周期终止、quiet 状态可达性、有效
根状态上的 Core 完全合流，以及可达 quiet normal form 的唯一性。Examples
还具体构造了旧 API provider 到新 provider ID 的替换，并证明 model consumer
的 committed binding 随之发生变化。

Integrated confluence 仍然没有被声称：不同 actor 的 Core 生命周期步骤可能
通过共享 effect world 发生交互，需要额外的 effect commutation 假设才能继续
证明。

## WSL 开发环境

本项目以 WSL 为主要开发环境，当前固定使用 Lean/mathlib `v4.33.0`。具体
版本、Lake 配置和工具链说明见 `TOOLING.md`。

## 构建与审计

```text
lake build Cordis.Core
lake build Cordis.Effects
lake build Cordis.Integrated
lake build Cordis.Extended
lake build Cordis.Examples
lake build
```

`Cordis/Audit.lean` 对各层具有代表性的强定理运行 `#print axioms`。项目策略
禁止 Lean 源码出现 `sorry`、`admit` 或自定义 `axiom` 声明。

## 核心建模选择

Committed provider 与 target provider 的有效性条件不同。正在 unloading 的
provider 仍然 installed，因此可以保留在 committed view 中；新选中的 target
provider 则必须 active。只有存在唯一 active candidate 时，provider resolution
才返回结果。Single-source 只约束当前 `registered` 集合，因此后续
orchestration epoch 可以用新的 ID 替换 provider。

## 范围与解读

在把任何定理解读为 Cordis 论文或实际实现的结论前，请先阅读
`LAYERS.md`、`ASSUMPTIONS.md` 和 `PAPER_MAP.md`。Core 合流定理、对抗性审计
和剩余边界记录在 `CONFLUENCE_STATUS.md`；当前实现状态见 `PLAN.md`，语义
决策见 `DESIGN_NOTES.md`。
