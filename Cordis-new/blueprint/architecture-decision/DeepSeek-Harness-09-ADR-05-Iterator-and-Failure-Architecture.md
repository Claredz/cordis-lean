# DeepSeek Harness ADR-05: Iterator and Failure Architecture

| Field | Value |
|---|---|
| Decision ID | `ADR-05` |
| Status | **Architecture accepted — spike compiled** |
| Artifact version | `1.0.0-accepted-compiler-validated` |
| Semantic closure status | **Carrier and execution boundary resolved; downstream lifecycle/control proofs pending** |
| Date | 2026-08-26 |
| Resolves | `BD-ITER` (iterator, continuation, folding, boundedness, and failure carrier) |
| Source | Shi, Zhang, and Cui, *A Programming Paradigm for Spatiotemporal Composability* |
| Source SHA-256 | `4d48478dc0b6222d9f74d7db10ee776449b1209eb112632336544d32a49db97f` |
| Depends on | ADR-01 (equivalence), ADR-02 (coeffect store/partiality), ADR-03 and ADR-03-CLOSURE (unified state), ADR-04 (incarnation identity and alpha action) |
| Companion artifacts | `DeepSeek-Harness-09-ADR-05-Iterator-and-Failure-Architecture.json`; `DeepSeek-Harness-09-ADR-05-Iterator-and-Failure-Architecture-Spike.lean` |
| Frozen baselines | Harness-03 `1.0-frozen`; Harness-04 `1.0-baseline` |

## 1. Decision

The theorem-facing iterator carrier is a **ranked continuation machine**.  A machine has
an external control-code type `Q`, a root code, a natural-number rank, and a runner

```text
run : Q → Γ → StageResult Γ Ξ Q
```

where a stage either:

```text
halt  δ undo                 -- successful final stage
yield δ undo next             -- successful stage with a chosen continuation
raise error                  -- failure at this boundary
```

Every `yield` must satisfy the certificate

```text
rank next < rank current.
```

The successor may depend on the current state, so this is a defunctionalized form of the
paper's state-dependent `Maybe I` continuation.  The rank certificate is the authoritative
termination/finite-work profile: every individual path is finite and has at most
`rank(root) + 1` stages.  An optional finite-node specialization may add a finite node
support/enumeration when D60 needs to enumerate all reachable control codes; no global
`Fintype` is assumed by the generic core.

Execution is a well-founded recursive fold over the rank.  Its result is

```text
success finalState totalUndo
failure error stateAtBoundary prefixUndo
```

For a successful stage with undo `u` followed by a continuation whose undo is `r`, the
folded undo is `u ∘ r`.  Thus the most recently executed inverse is applied first (LIFO),
exactly as required by Definition 52.  A failed stage contributes no new inverse; the
already accumulated prefix inverse is retained and is consumed by the later lifecycle
unload rule.

The literal recursive equation `μ I. Γ → Γ × (Γ → Γ) × Maybe I` is therefore not copied as
a Lean inductive type.  It remains the paper-level notation and a possible refinement
source.  The accepted core is an executable, rank-certified representation of finite
continuation behavior.  An unbounded coinductive/productivity profile is outside this
ADR and would require a superseding decision rather than silently weakening the T66
termination assumptions.

## 2. Why this decision is necessary

Definition 51 introduces a recursive iterator and a greatest-style observational relation
on iterators.  Definition 52 recursively applies a continuation and folds inverses.  The
paper later defines continuation reach and a length bound in D60, and T66 assumes a uniform
finite iterator length.  The failure refinement replaces the successful result with an
`Either` and sends the accumulated undo to `L-Raise`/`L-Unload`.

Three choices that are harmless in prose become global formalization blockers:

1. **A recursive type is not a termination proof.**  A raw `μ` equation admits a recursive
   object that may keep yielding forever.  It does not provide the well-founded recursion
   required by D52 or the finite bound required by T66.
2. **The continuation is state-dependent.**  Replacing it by a single fixed list would be
   easy to execute, but would silently remove the paper's ability to choose the next
   iterator from the current state.  The node runner retains that branching explicitly.
3. **Failure is not absence and not identity.**  A failing prefix has an error and an
   accumulated recovery action.  Erasing it to `none`, or returning the identity inverse,
   loses the state on which `L-Raise` operates and can make a false recovery theorem look
   true.

The ranked machine addresses these points while keeping arbitrary action/inverse code out
of the recursive `RawState` carrier selected by ADR-03.

## 3. Normative architecture

### 3.1 Stage and machine boundary

`Q` is a control-code/index type.  It is not a fiber name, an incarnation ID, or a
`RawState`; the machine may be stored in a component/action program or supplied by the
control interpreter.  A stage has exactly one of the following outcomes:

| Outcome | State change | Continuation | Failure payload |
|---|---|---|---|
| `halt δ g` | successful transition to `δ` | none | none |
| `yield δ g q'` | successful transition to `δ` | `q'`, with lower rank | none |
| `raise ξ` | no new stage state/inverse | none | `ξ` |

The last row means “the failing boundary did not yield a witnessed successful effect.”
If an implementation performs preliminary work before reporting an error, that work must
be represented as an earlier successful stage or as an explicit atomic action in the
control semantics; it must not be hidden in `raise`.

### 3.2 Rank and finite execution

The machine carries

```text
rank : Q → Nat
next_lt : run q γ = yield δ g q' → rank q' < rank q.
```

The rank is a certificate, not an operational counter.  It is sufficient for Lean's
well-founded recursion and gives the executable upper bound

```text
edgeBound(q)  = rank(q)
stageBound(q) = rank(q) + 1.
```

The distinction is deliberate: the paper's `len(i)` prose does not make it completely
clear whether the current stage or only continuation edges are counted.  The blueprint
uses `stageBound` for T66-style hypotheses and records the edge/stage convention explicitly
when instantiating a theorem.

The generic carrier does not require `Q` itself to be finite.  If a theorem must enumerate
all possible continuations, an integration profile supplies a finite closed node support
(or a `Fintype Q` instance) and a computable runner.  Path finiteness and node-set
finiteness are separate assumptions.

### 3.3 Execution and inverse folding

Let `execFrom q γ` be defined by well-founded recursion on `rank(q)`:

```text
raise ξ       ↦ failure ξ γ id
halt δ g      ↦ success δ g
yield δ g q'  ↦
  let r be execFrom q' δ
  combine r with undo (g ∘ r.undo)
```

The failure branch of the recursive continuation still returns its prefix undo:

```text
failure ξ ε r ↦ failure ξ ε (g ∘ r).
```

Composition is written in application order: `(g ∘ r) x = g (r x)`.  Consequently the
continuation's inverse `r` runs before the current stage's inverse `g`; this is the LIFO
recovery order of D52 and of the runtime disposer stack.

The one-stage/plain-effect embedding is a machine whose root has rank zero and always
returns `halt`.  Thus ordinary witnessed effects are a specialization, not a second
effect tower or a duplicated execution semantics.

### 3.4 Failure and partiality

The authoritative result type preserves three pieces of failure information:

```text
error       : Ξ
state       : Γ       -- state at the failing boundary
prefixUndo  : Γ → Γ  -- recovers the successful prefix
```

The success-only projection

```text
execOption : Iterator → Γ → Option (Γ × (Γ → Γ))
```

is merely an observation/projection: it returns `some` for successful completion and
`none` for failure.  It is not the execution carrier and it never supplies an identity
inverse on failure.  This follows ADR-02's separation of semantic partiality from
diagnostic `Except` information.

The error relation is exact (`ξ = ξ'`) in the default observation.  A later diagnostic
profile may supply a coarser error relation, but it must state that choice explicitly and
must not silently identify success with failure.

The paper's lifecycle reading is retained: a failed fiber is an `Inactive(error)` state,
has no committed view, blocks no other fiber, and is not retried by `L-Begin` unless a
future control ADR explicitly adds a retry protocol.  These lifecycle constructors are
not encoded in this carrier; BD-CONTROL consumes `ExecResult`.

### 3.5 Observational relation and iterator bisimulation

For a state relation `R : Γ → Γ → Prop`, a returned inverse is compared by the
cross-pointwise relation

```text
PointwiseRel R f g := ∀ {x y}, R x y → R (f x) (g y).
```

The stage relation compares:

- `halt` with `halt`, relating states and inverses;
- `yield` with `yield`, relating states, inverses, and continuation codes;
- `raise` with `raise`, using the selected error relation;
- no success/failure cross-case.

The local `StepLawful` contract uses equality of the same control code.  The general
`StageRelC`/`IteratorBisim` interface allows a continuation relation `C : Q → Q → Prop`;
this is the Lean-facing replacement for the paper's greatest iterator relation.  The
ranked carrier makes the evaluator finite; proving that a chosen `C` is a bisimulation and
that it transports rank/continuation witnesses remains an integration theorem, not an
implicit property of `μ`.

The inverse witness is success-only:

```text
R (g δ) γ
```

for `halt δ g` and `yield δ g q'`.  `raise` has no `δ` or `g`, so no witness clause is
invented for it.

### 3.6 Reach, length, and transformation generators

`hasNext q q'` is existential over all input states and successful yielded stages.  Its
reflexive-transitive closure `Reach` is therefore the least continuation closure over
possible states, matching D60 rather than recording only one concrete execution.

The spike proves the rank monotonicity lemma

```text
Reach q q' → rank(q') ≤ rank(q).
```

The exact semantic length may be defined later as the supremum/minimal uniform bound over
all reachable states.  The executable `stageCountFrom` and `stageCountFrom_le` provide a
sound rank certificate now.  A uniform bound used by T66 is an explicit predicate:

```text
UniformlyBounded it K :=
  ∀ q γ, Reach root q → stageCountFrom q γ ≤ K.
```

The rank-derived bound `rank(root)+1` discharges this predicate in the generic profile.

Because a failing iterator has no total `pr1 ∘ i`, D60's transformation generators are
represented first as **successful stage graph edges** and their reflexive-transitive
closure.  For a total deterministic nonfailing specialization, these graphs can be
reified as functions and the familiar `Submonoid (Function.End Γ)` formulation can be
proved as a refinement.  This avoids the paper's underspecified “read the Right branch”
operation on `Either`.

Independence is a separate relation-level certificate over the selected generators.  It
must include map commutation modulo `R`, stability of returned inverses, and stability of
continuation choices under a foreign transformation.  The existence of a monoid/graph
closure alone does not imply iterator independence.

### 3.7 Integration with ADR-03 and ADR-04

The iterator program, control code, rank certificate, and interpreter environment are
external to the recursive `RawState`/`FiberCell` data.  A `FiberCell` may refer to an
opaque action/iterator code or token; it must not contain an unrestricted
`RawState → RawState` behavior that recreates the negative State/Registry/Fiber cycle.

An incarnation ID from ADR-04 is a name-bearing identity in lifecycle labels and trace
metadata, not a control node `Q`.  If a continuation allocates a child, the later
BD-CONTROL label must expose the owner and fresh incarnation; the ranked iterator itself
does not authorize hidden name allocation.

Alpha-renaming acts on all name-bearing state/trace fields.  The iterator code is
name-neutral only under an explicit payload/interpreter opacity assumption.  If code or
ambient data captures an incarnation, the refinement must provide a rename action and
prove interpreter equivariance; this ADR does not assume that closure for free.

### 3.8 Boundary with asynchrony and control

Iteration is a finite computation plan.  Asynchrony is a property of launch/landing traces
and host inertia, not another iterator constructor.  `L-Divert` therefore belongs to
BD-CONTROL and may either abort at a boundary or admit a landing continuation under an
explicit in-flight witness.  The current machine does not claim to prove asynchronous
landing safety.

Similarly, lifecycle-only progress theorems must range over a suffix beginning at an
arbitrary reachable state.  A trace definition that starts with an empty registry and
requires every step to be a lifecycle step is vacuous for orchestration-created fibers.
If orchestration turns are interleaved, T66 must state a finite input/orchestration budget
and include those labelled turns in its step bound.  These are control-scope repairs, not
additional iterator constructors.

## 4. Mapping to the paper

| Paper item | Accepted formal boundary |
|---|---|
| D51 witnessed effect iterators | `RankedIterator`, `StageResult`, rank-decrease certificate, `StageWitness`, `StageRelC`, `IteratorBisim` |
| D52 effect-iterator transformation | `execFrom`, `exec`, `composeUndo`, `foldUndo`; well-founded rank recursion and LIFO inverse composition |
| `R.iter` / L-Begin, L-Iter, L-Finish | Control-layer consumers of successful `ExecResult`; iterator subfamily of the authoritative full relation |
| `R.fail` / L-Raise | `StageResult.raise`, `ExecResult.failure`, success-only witness, prefix undo carried to control/unload |
| D60 reach and length | `hasNext`, `Reach`, `stageCountFrom`, rank-derived `UniformlyBounded`; exact supremum remains a semantic wrapper |
| D60 transformation monoid | Successful stage graph and closure first; function-monoid reification only under total deterministic specialization |
| T61/T64 recovery | Consume `ExecResult` and the ADR-01 relation; require iterator independence and inverse-properness hypotheses explicitly |
| T66 per-fiber bound | Use `UniformlyBounded it K`; choose `K` with the documented stage/edge convention and add finite orchestration/name support from BD-CONTROL/BD-NAMES |

The ranked machine is therefore a **formalization repair/refinement profile**, not a claim
that the paper's unqualified recursive object is already finite.  Any theorem stated for
the literal unbounded/coinductive reading needs a separate carrier and proof.

## 5. Alternatives considered

| Alternative | Decision | Reason |
|---|---|---|
| Copy the literal `μ I` equation as a Lean recursive type | **Rejected for core** | It does not choose least versus greatest/productive behavior, and hidden recursive calls are not an executable termination certificate. |
| Coinductive stream/tree as the default | Deferred/rejected for current core | It models potentially infinite behavior but cannot discharge the finite T66 profile without an additional productivity/boundedness layer. |
| Plain `List` of stage runners | Allowed as a subprofile, rejected as authoritative | It is easy to execute but loses state-dependent continuation selection unless a separate control compilation theorem is added. |
| Fuel-only interpreter | Rejected as the semantic carrier | Fuel makes evaluation total but can truncate a valid iterator; it is an implementation technique for the ranked evaluator, not the iterator's invariant. |
| Ranked continuation machine | **Accepted** | Preserves state-dependent branching, gives structural/well-founded execution, exposes a finite bound, and keeps code outside `RawState`. |
| General `WellFounded` successor relation | Deferred extension | More general than a Nat rank, but the current theorem target needs an executable uniform finite bound. It can be added behind the same stage/result API in a superseding ADR. |
| Failure as `Option` or identity inverse | Rejected | It erases error/state/prefix-recovery information and invalidates L-Raise/L-Unload reasoning. |
| Store iterator/undo closures directly in `RawState` | Rejected | Reintroduces the negative recursive State/Registry/Fiber cycle already repaired by ADR-03. |

## 6. Lean-facing spike

The standalone companion uses namespace `CordisADR05` and imports `Mathlib.Tactic`.  It
contains:

```text
StageResult, RankedIterator, ExecResult
composeUndo, execFrom, exec
execFrom_raise, execFrom_halt, plainEffect, exec_plainEffect
stageCountFrom, stageCountFrom_le
edgeLengthBound, stageLengthBound
hasNext, Reach, reachableFromRoot, reach_rank_le
UniformlyBounded, root_uniformlyBounded
execOption, execOption_raise
successfulAt, generatorEdge, TransformClosure
PointwiseRel, StageRel, StageRelC, IteratorBisim, ExecRel
StepLawful, InverseProper, StageWitness, foldUndo
```

Compiler-checked evidence includes:

- well-founded execution over strictly decreasing ranks;
- exact `raise` and `halt` equations;
- plain-effect embedding;
- rank-derived stage-count bound;
- continuation reach closure and rank monotonicity;
- uniform root bound;
- failure-only projection to `none` without identity fallback;
- successful-stage graph closure with identity and composition;
- relation-parametric stage/iterator observation contracts;
- LIFO fold orientation;
- a concrete two-stage state-dependent continuation smoke test.

The spike intentionally does not prove the full lifecycle rules, T61/T64/T66, asynchronous
landing, or D60's final independence theorem.  Those require the control/staging/name
constructors and the ADR-01 observational relation to be instantiated.

## 7. Acceptance gates and remaining obligations

| Gate | Result |
|---|---|
| `ITER-01` No literal mixed-variance/fixed-point type in the executable core | represented and compiled |
| `ITER-02` State-dependent continuation choice | represented by `yield ... next` and smoke-tested |
| `ITER-03` Explicit finite termination certificate | rank and strict-decrease witness compiled |
| `ITER-04` Executable one-step/fold semantics | `execFrom`/`exec` compiled |
| `ITER-05` Correct LIFO inverse accumulation | composition and fold orientation compiled |
| `ITER-06` Failure carries error, boundary state, and prefix undo | `ExecResult.failure` and raise equations compiled |
| `ITER-07` No success/failure identity erasure | success-only `execOption` projection compiled |
| `ITER-08` Relation/bisimulation boundary | `StageRelC`/`IteratorBisim` contracts compiled |
| `ITER-09` Reach and bounded-length interface | `Reach`, rank monotonicity, and uniform bound compiled |
| `ITER-10` Failure-safe D60 generator boundary | successful graph closure represented; function reification deferred |
| `ITER-11` ADR-03/04 state and identity boundaries preserved | no frozen carrier or baseline mutation |
| `ITER-12` Pinned Lean compile/no placeholders | passed locally; exit code 0 (warnings only) |

Pending obligations are explicit:

- instantiate `StageWitness` and `StepLawful` for component actions;
- prove execution respects ADR-01 observational equivalence under the selected
  continuation bisimulation;
- define exact semantic `len` and reify graph generators to function monoids where the
  nonfailing/total hypotheses hold;
- state and prove iterator independence, including inverse and continuation stability;
- add BD-CONTROL's L-Begin/L-Iter/L-Finish/L-Divert/L-Raise constructors;
- repair T66 to a reachable lifecycle suffix (and, if needed, a finite mixed orchestration
  trace) with finite incarnation support from ADR-04;
- connect runtime asynchronous callbacks to the ranked plan via an in-flight refinement.

“Accepted” means that the global iterator/failure representation is fixed and its Lean
boundary compiles.  It does not claim that every downstream lifecycle theorem is already
proved.

## 8. Readiness effect

Harness-03 and Harness-04 are immutable; ADR-05 changes neither dependency edges nor the
disposition file.  It removes `BD-ITER` only from blocker sets where no independent blocker
remains.  The affected rows become:

```text
D43      BD-STATE, BD-COEFFECT
D44      BD-STATE, BD-STAGING
D48      BD-STATE, BD-EQUIV
D49      BD-STATE, BD-STAGING, BD-CONTROL
D51      BD-EQUIV
D52      BD-EQUIV
D60      BD-EQUIV, BD-CONTROL
T64      BD-EQUIV, BD-CONTROL
T66      BD-CONTROL
T73      BD-SUPPORT, BD-EQUIV, BD-CONTROL
D69      BD-COEFFECT
R.iter   BD-CONTROL
A.async  BD-CONTROL
R.fail   BD-EQUIV, BD-CONTROL
R.full   BD-STATE, BD-STAGING, BD-CONTROL
```

No disposition row is silently marked fully proved merely because the iterator carrier
compiled.  In particular, `BD-EQUIV`, `BD-CONTROL`, `BD-STAGING`, and `BD-SUPPORT` remain
independent decisions.

The next natural decision is `BD-CONTROL` or `BD-STAGING`, depending on whether the team
wants to encode the labelled lifecycle relation before the in-flight/committed-view
staging boundary.  This ADR does not choose that order.

## 9. Revision policy

- Editorial clarification with the same ranked carrier: patch version only.
- Additional executable lemmas or a corrected spike retaining the carrier: minor revision.
- Replacing rank with an unbounded/coinductive default, changing failure to an identity
  projection, or moving iterator code into `RawState`: superseding ADR required.
- Frozen Harness-03/04 and accepted ADR-01/02/03/04 artifacts remain unchanged.

