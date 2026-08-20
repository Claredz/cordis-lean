# CordisLean proof-engineering tooling

## Pinned environment

- Lean toolchain: `leanprover/lean4:v4.33.0` (from `lean-toolchain`)
- Lean commit: `d8b18978322de05a8f3dba51ef03cf5461676c17`
- Lake: `5.0.0-src+d8b1897`
- mathlib release: `v4.33.0` (from `lakefile.toml`)
- mathlib commit: `db584cd6d46c92f209a44c0f1c829460d327499d`
- Project root used by the existing scaffold:
  `/mnt/e/ALL/学习/简历/cordis-lean`
- Windows Elan installation exposed to WSL:
  `/mnt/c/Users/claredz/.elan/bin`

The project originally requested v4.32.1. On 2026-08-20 the user explicitly
selected the already installed v4.33.0 toolchain instead; mathlib was moved to
the matching release at the same time. The resolved commit above is referenced
by the official `v4.33.0` release tag (and by `master-2026-08-10`).

## Lean LSP and MCP

This Codex session provides a Lean LSP MCP server. Its available project tools
are:

```text
lean_build
lean_code_actions
lean_completions
lean_declaration_file
lean_diagnostic_messages
lean_file_outline
lean_get_widget_source
lean_get_widgets
lean_goal
lean_hammer_premise
lean_hover_info
lean_leanfinder
lean_leansearch
lean_local_search
lean_loogle
lean_minimal_hypotheses
lean_multi_attempt
lean_profile_proof
lean_references
lean_run_code
lean_state_search
lean_term_goal
lean_verify
```

MCP is a development aid only. No Lean module, lake target, or build step may
depend on it. The installed server is `lean-lsp-mcp 0.29.0`, pinned in the
Codex MCP configuration. WSL command shims for `lean`, `lake`, and `elan` are
present both in `/home/claredz/.local/bin` and beside the Windows Elan shims so
that MCP subprocesses can resolve the extensionless command names. The smoke
test and its result are recorded below after execution.

## Theorem-proving skill

On 2026-08-20, the installed Codex skill catalog and the official curated skill
list contained no Lean 4 theorem-proving skill. The experimental-list endpoint
was unavailable. After reviewing the community candidates, the user selected
`cameronfreer/lean4-skills`; its core Codex skill was installed as `lean4` from
`plugins/lean4/skills/lean4`. Codex discovers a newly installed skill on the
next turn. Project semantic decisions remain governed by `AGENTS.md` and the
Cordis plan, not by the generic skill.

## API-search workflow

1. Search CordisLean with `rg` or Lean MCP local search.
2. Confirm candidates with `#check`/hover and inspect exact arguments.
3. Use `#find`, `exact?`, `apply?`, `simp?`, or a small isolated snippet.
4. Search local mathlib sources.
5. Use LeanSearch/Loogle only when local search is insufficient.
6. Add a generic local lemma only after confirming no suitable API exists.

Useful mathlib abstractions include `Relation.TransGen`,
`Relation.ReflTransGen`, `Relation.ReflGen`, `WellFounded`, `Acc`, `Finset`,
`Fintype`, `Multiset`, and lexicographic well-founded orders.

## Commands

From the project root:

```bash
lean --version
lake --version
lake exe cache get
lake build
```

For a focused check:

```bash
lake env lean Cordis/Core/Basic.lean
```

If WSL command lookup does not expose Windows Elan shims, invoke
`/mnt/c/Users/claredz/.elan/bin/lean.exe` and `lake.exe` directly or restore the
project's documented WSL shims. If MCP is unavailable in a later session, use
`#check`/`#find`/`exact?`/`apply?`, local source search, and `lake build`; do not
block proof work on MCP repair.

## Verification log

- Lean 4.33.0 toolchain: installed and version-checked.
- Abandoned Lean 4.32.1 download: stopped; two partial temporary archives
  (80,073,582 bytes total) and its stale Elan lock were deleted.
- `lean-lsp-mcp`: version 0.29.0 installed, version-pinned, and PATH repaired.
- `lean4` theorem-proving skill: installed; activation begins on the next turn.
- `lake update`: succeeded; all mathlib release dependencies resolved.
- mathlib cache: 8,690 files downloaded and decompressed successfully.
- Command-line smoke theorem: compiled successfully.
- Lean LSP/MCP smoke test: passed `lean_run_code`, exact goal inspection,
  mathlib declaration search, three-way `lean_multi_attempt`, clean error
  diagnostics, `lean_verify`, and `lean_build`.
- Smoke theorem axiom/source audit: no axioms and no suspicious source patterns.
- Final full `lake build`: succeeded (8,736 jobs including cached
  dependencies).
- Final `lake build Cordis.Audit`: succeeded (8,740 jobs); representative
  strongest results use at most `propext`, `Classical.choice`, and `Quot.sound`.
- Final frozen-Core regression `lake build Cordis.Core`: succeeded (8,714
  jobs).
- Lean source placeholder scan: no `sorry`, `admit`, or custom `axiom`
  declarations.
