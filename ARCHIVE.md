# Archive and migration notes

This repository contains two distinct generations of Cordis formalization work.

## Legacy mechanization

The original project developed a simplified finite lifecycle/dependency model under the dependency chain

```text
Core → Effects → Integrated → Extended → Examples
```

It proved substantial results including well-formedness preservation, withdrawal safety, lifecycle termination, quiet-state reachability, Core confluence and explicit provider replacement. Those results remain useful as mechanically checked examples and as a source of proof-engineering experience.

However, this model was intentionally narrower than the 2026 paper and the production Cordis runtime. In particular, it fixed a simplified catalog/provider discipline and did not directly formalize the paper's complete effect/coeffect hierarchy, iterator semantics, realms, asynchronous behavior, failure semantics, dynamic registration or implementation refinement.

The frozen legacy snapshot is:

```text
branch: archive/legacy-formalization-2026-08-24
commit: afa8a0e29513c8be34878e054fa18f36def5fa6f
```

The historical branch `codex/initial-upload` currently points to the same snapshot and is deprecated.

## Current paper-first formalization

The active project started from a fresh audit of Shi, Zhang, and Cui, *A Programming Paradigm for Spatiotemporal Composability*.

The current workflow is:

```text
formal reference
→ frozen definition/theorem dependency graph
→ per-item formalization disposition
→ architecture decisions and compile spikes
→ production Lean modules
→ metatheory
→ runtime refinement
```

The new work deliberately distinguishes:

- the literal paper statement;
- a repaired formal target when the paper statement is ill-typed, vacuous, non-computable, ambiguous or overstrong;
- the resulting Lean semantics;
- the behavior actually guaranteed by the Cordis TypeScript runtime.

No legacy theorem should be cited as a proof of a paper theorem merely because the concepts have similar names. Conversely, the legacy mechanization should not be deleted: it is an archived mathematical model with its own proved claims.

## Migration policy

During the transition, legacy source files remain in the working tree so their last verified build continues to serve as a regression/reference target. They are logically archived even before a physical directory move.

A later cleanup may move them under `Cordis/Legacy/`. Such a move should be performed only when imports, Lake targets, documentation and CI can be updated atomically. Directory aesthetics are not worth breaking a known-good proof corpus.

New production code must not be added to legacy namespaces unless it is explicitly a repair of the legacy archive itself.
