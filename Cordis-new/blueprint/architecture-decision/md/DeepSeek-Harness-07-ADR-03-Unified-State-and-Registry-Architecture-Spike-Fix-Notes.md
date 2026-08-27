# ADR-03 Unified State and Registry Spike 修复说明

## 文件

- 原始文件：`DeepSeek-Harness-07-ADR-03-Unified-State-and-Registry-Architecture-Spike.lean`
- 修复文件：`DeepSeek-Harness-07-ADR-03-Unified-State-and-Registry-Architecture-Spike-Fixed.lean`
- 验证环境：Lean 4.33.0，项目当前锁定的 Mathlib/Lake 环境

原始附件保持不变。修复版本位于仓库的 `Scratch/` 目录。

## 故障表现

原文件的第一个有效错误出现在 `Registry` 定义处：

```text
typeclass instance problem is stuck
  DecidableEq (?m.12 x)
```

后续 `RawState`、`Finmap.lookup`、字段投影、更新函数等位置出现了近百条错误。这些
不是互相独立的问题，而是 `Registry` 未能成功定义之后产生的级联错误。

## 根因

原始定义依赖外层 section 变量：

```lean
abbrev Fiber :=
  FiberCell IncarnationId Key Value ComponentCode BehaviorCode AccumulatorCode Life

abbrev Registry := Finmap (fun _ : IncarnationId => Fiber)
```

Lean 会自动把 `Fiber` 使用的外层变量泛化为隐式参数。因此，`Fiber` 实际上不是当前
section 中一个已经固定的类型，而是一个多态类型函数，其完整形状近似为：

```lean
@Fiber :
  {IncarnationId : Type u} ->
  {Key : Type u} ->
  {ComponentCode BehaviorCode AccumulatorCode Life : Type u} ->
  {Value : Key -> Type v} ->
  [DecidableEq Key] ->
  Type _
```

在 `Finmap (fun _ : IncarnationId => Fiber)` 中，预期类型只能告诉 Lean `Fiber` 最终应当
是某个 `Type`，却不能反推出它的 `Key`、`Value` 和代码类型参数。于是实例搜索看到的
不是已经存在的 `DecidableEq Key`，而是 `DecidableEq ?m`。由于 `?m` 尚未确定，实例
搜索按规则停止。

因此，问题不是缺少一个新的 `DecidableEq` 实例。添加更多实例、使用
`noncomputable section`，或者在后续证明中加入 `classical` 都不能修复这个首错。

同样的裸类型别名模式还存在于 `Registry`、`RawState`、`TrackedContext`、
`ActionSemantics`、`StateMap` 和 `ControlEdit`，所以只修补最早的 `Fiber` 使用仍会在
下一层遇到相同的参数推断问题。

## 主要修复

### 1. 显式参数化状态载体

`Fiber`、`Registry` 和 `RawState` 现在显式声明所有决定其类型的参数：

```lean
abbrev Fiber (IncarnationId Key : Type u) (Value : Key -> Type v)
    (ComponentCode BehaviorCode AccumulatorCode Life : Type u) [DecidableEq Key] :=
  FiberCell IncarnationId Key Value ComponentCode BehaviorCode AccumulatorCode Life

abbrev Registry (IncarnationId Key : Type u) (Value : Key -> Type v)
    (ComponentCode BehaviorCode AccumulatorCode Life : Type u) [DecidableEq Key] :=
  Finmap (fun _ : IncarnationId =>
    Fiber IncarnationId Key Value ComponentCode BehaviorCode AccumulatorCode Life)
```

`RawState` 采用同样的显式参数形式。这与仓库中 `Core.State FiberId Key` 的现有使用方式
一致：先确定索引类型，再让 Lean 合成对应的 `DecidableEq`。

### 2. 使用局部短记号保持主体可读

文件内部增加了以下局部记号：

```lean
local notation "FiberT" => Fiber IncarnationId Key Value ...
local notation "RegistryT" => Registry IncarnationId Key Value ...
local notation "RawStateT" => RawState Ambient IncarnationId Key Value ...
```

这些记号只在当前文件中使用，不会污染对外 API。所有谓词、查询和 registry 更新函数
都改为接收已经专门化的 `FiberT`、`RegistryT` 或 `RawStateT`。

### 3. 显式参数化后续载体

`TrackedContext` 和 `ActionSemantics` 同样改为显式参数化结构，并分别使用
`TrackedContextT` 和 `ActionSemanticsT` 局部记号。

`StateMap` 与 `ControlEdit` 改为普通的状态类型构造器：

```lean
abbrev StateMap (State : Type*) := State -> State
abbrev ControlEdit (State : Type*) := State -> State
```

调用处使用 `StateMap RawStateT` 和 `ControlEdit RawStateT`，不再依赖 Lean 从一个裸别名
中猜测完整状态参数。

## 附带的 elaboration 修复

除核心参数化修复外，还处理了以下由当前 Lean 版本暴露的问题：

1. `activeUnionAux` 直接对 `policy.providesNow c.lifecycle : Bool` 分支，避免为已封装成
   `Prop` 的 `contributesNow policy c` 额外搜索 `Decidable`。
2. `seededCoeffect_empty` 将 `emptyRaw ambient` 标注为 `RawStateT`，提前固定所有隐式参数。
3. `modifyFiber_ambient` 显式拆分 `Finmap.lookup` 的两个 match 分支，再以 `rfl` 关闭。
4. `targetEligible` 的未使用参数改名为 `_policy`。
5. `composeStep_apply` 使用 `omit [DecidableEq IncarnationId] in`，避免携带未使用的实例
   参数。

第 1 项没有改变语义，因为原谓词的定义正是：

```lean
policy.providesNow c.lifecycle = true
```

其余修改只向 elaborator 提供类型信息或调整证明脚本。

## API 影响

外部代码不能再把 `Fiber`、`Registry` 或 `RawState` 当作无参数类型裸用。应显式提供参数，
例如：

```lean
Fiber IncarnationId Key Value ComponentCode BehaviorCode AccumulatorCode Life

Registry IncarnationId Key Value ComponentCode BehaviorCode AccumulatorCode Life

RawState Ambient IncarnationId Key Value
  ComponentCode BehaviorCode AccumulatorCode Life
```

`DecidableEq Key` 仍由类型类系统从调用上下文中提供。`Finmap.lookup`、`insert` 和 `erase`
还需要调用上下文中的 `DecidableEq IncarnationId`，与修复前的设计意图一致。

## 语义边界

本次修复没有：

- 修改 `WellFormed` 的逻辑内容；
- 增加或隐藏 acyclicity 假设；
- 把 committed provider 从 installed 加强为 active；
- 改变 target provider 必须 active 的设计；
- 将 Core 结论扩张为 full Cordis 结论；
- 引入 `sorry`、`admit` 或项目自定义 `axiom`。

## 验证

单文件检查：

```bash
lake env lean \
  Scratch/DeepSeek-Harness-07-ADR-03-Unified-State-and-Registry-Architecture-Spike-Fixed.lean
```

结果：通过，无错误、无警告。

占位符扫描：

```bash
rg -n '\b(sorry|admit|axiom)\b' \
  Scratch/DeepSeek-Harness-07-ADR-03-Unified-State-and-Registry-Architecture-Spike-Fixed.lean
```

结果：无匹配。

项目回归检查：

```bash
lake build
```

结果：`Build completed successfully (8738 jobs)`。构建输出中的提示均来自仓库原有文件，
修复文件自身没有新增诊断。
