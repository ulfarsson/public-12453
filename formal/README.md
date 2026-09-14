# `formal/` — the Lean 4 certificate

A machine-checked development, in Lean 4 with Mathlib, of the correctness half of the
paper *Protected tails and polynomial-time enumeration of permutations avoiding a direct sum of an increasing pattern and 231*
(`paper/av12453_polytime.tex`).  Two chains are certified end to end:

| `d` | class | literal recurrence | kernel algorithm |
|---|---|---|---|
| 1 | `Av(1342)` | `OneThreshold.av1342_count : W n [] = (avoiders n (beta 1)).card` | `OneThreshold.av1342_count_kernel : G n = (avoiders n (beta 1)).card` |
| 2 | `Av(12453)` | `TwoThreshold.av12453_count : H (n, 0) [] = (avoiders n (beta 2)).card` | `TwoThreshold.av12453_count_kernel : G (n, 0) = (avoiders n (beta 2)).card` |

`avoiders n τ` is the finset of permutations of `{0, …, n-1}` avoiding `τ`, and
`beta d = ι_d ⊕ 231` (`beta 1 = [0,2,3,1] = 1342`, `beta 2 = [0,1,3,4,2] = 12453`,
`0`-based).  The `d = 2` kernel theorem certifies the *values* of the paper's unreduced `d = 2`
kernel recurrence (eq:K, eq:D, eq:G, eq:answer-G), i.e. the mathematical content of the
polynomial-time algorithm.  Not formalized: any complexity bound (the Lean `K` and `G`
are fuel-driven recursions, not the memoized sparse-row program), the two translation
quotients of the paper's Section 7 that give `O(N^7)`/`O(N^4)` for `12453`, and the
program `code/av12453_fast_rns.cpp` that produced the published `n = 150` and `n = 300`
data.  See `AUDIT_2026-09-05.md` for the trusted base a referee must check by eye.

Everything is `sorry`-free and uses only Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

## Modules

Built in dependency order; `Av12453/Av12453.lean` imports all twenty.

| component | module | lines | headline results (paper) |
|---|---|---:|---|
| 1–2 | `Av12453/Basic.lean` | 951 | words, `OrderIso`, `Contains`/`Avoids`, `perms`, `avoiders`, `beta` |
| 1–2 | `Av12453/Trigger.lean` | 277 | `avoids_beta_iff` — the trigger lemma (`lem:trigger`) |
| 1–2 | `Av12453/FirstLetter.lean` | 350 | the first-letter lemma for `Av(231)` (`lem:first-letter`) |
| 3a | `Av12453/OneThreshold/Defs.lean` | 1282 | the `d = 1` scan, the state `(p, L)`, the literal recurrence `W` (`eq:W`) |
| 3a | `…/OneThreshold/Invariant.lean` | 358 | (A) the separation invariant (`lem:1342-separators`) |
| 3a | `…/OneThreshold/Semantics.lean` | 403 | (B) deferred letters have no completion; (C) legal complete words avoid `1342` |
| 3a | `…/OneThreshold/Counting.lean` | 452 | (D) `A_eq_W`, and **`av1342_count`** (`thm:literal` at `d = 1`) |
| 4a | `…/OneThreshold/Kernel.lean` | 298 | `K`, `D`, `G` and `K_zero`/`K_succ_eq`/`D_one`/`D_succ`/`G_eq` (`eq:scalar-K`–`eq:scalar-G`) |
| 4a | `…/OneThreshold/KernelSupport.lean` | 296 | `K_support_eq` (`eq:scalar-support`), `K_diag_eq_catalan`, range extension |
| 4a | `…/OneThreshold/KernelFactor.lean` | 229 | `W_factor` (`eq:scalar-factorization`) |
| 4a | `…/OneThreshold/KernelCount.lean` | 247 | `G_eq_W`, **`av1342_count_kernel`** (`thm:scalar-algorithm`, correctness half) |
| 3b | `…/TwoThreshold/Thresholds.lean` | 748 | the threshold API `b₁ < b₂`, bands, control, `lem:least-trigger-frontier` |
| 3b | `…/TwoThreshold/Defs.lean` | 1247 | the `d = 2` scan and the literal recurrence `H` (`eq:H`, `eq:initial-terminal`) |
| 3b | `…/TwoThreshold/Invariant.lean` | 455 | (A) the separation invariant at `d = 2` (`cor:separators`) |
| 3b | `…/TwoThreshold/Semantics.lean` | 400 | (B) and (C) at `d = 2` |
| 3b | `…/TwoThreshold/Counting.lean` | 586 | (D) `A_eq_H`, and **`av12453_count`** (`thm:literal` at `d = 2`) |
| 4b | `…/TwoThreshold/Kernel.lean` | 454 | `ctrls`/`S`, `K`, `D`, `G` and their equations (`eq:K`, `eq:D`, `eq:G`) |
| 4b | `…/TwoThreshold/KernelSupport.lean` | 365 | `K_eq_zero_of_mass_lt`, `K_support` (`lem:support`, `eq:support`), range extension |
| 4b | `…/TwoThreshold/KernelFactor.lean` | 432 | `H_factor` (`eq:factorization`), the layer identity `K_ℓ((0,q),(0,s)) = K^{(1)}_ℓ(q,s)` |
| 4b | `…/TwoThreshold/KernelCount.lean` | 307 | `G_eq_H`, **`av12453_count_kernel`** (`eq:answer-G` at `d = 2`) |

10 137 lines of Lean in the twenty modules (plus 84 lines of `Av12453/Axioms.lean`, which
is not part of the library).

## Reports and briefs

The per-component development briefs and reports that guided the development were removed on
2026-09-06 (they remain in git history).  The closing assessment of the whole `d = 2`
certificate, the trusted base a referee must check by eye, and the audit findings are in
`AUDIT_2026-09-05.md`.

## Building and auditing

```sh
export PATH="$HOME/.elan/bin:$PATH"
cd formal/Av12453
lake build                              # full build; ~9 min cold, seconds warm
lake env lean Av12453/Axioms.lean       # axiom sweep over all twenty modules
```

`lake build` must finish with no errors and no warnings.  `Axioms.lean` walks *every*
constant declared in the twenty modules — including `private` declarations and
auto-generated constants; `example`s declare no constant and are outside the sweep, but no
theorem can depend on them — reports the axioms each depends on, and **throws an error** if
any depends on `sorryAx` or on an axiom outside `{propext, Classical.choice, Quot.sound}`.
It ends with a `checked N declarations in […]` line; exit code `0` is the audit passing.

Never run `lake update` or `lake exe cache get`, and do not touch `.lake/packages`: the
toolchain (`lean-toolchain`) and the Mathlib revision (`lake-manifest.json`) are pinned.

To re-derive the numbers rather than trust them, the `#eval`/`decide` blocks at the end of
each `Kernel*.lean` print the first terms of `|Av_n(1342)|` and `|Av_n(12453)|` from the
kernel tables; `OneThreshold/Counting.lean` and `TwoThreshold/Counting.lean` compare them
with brute-force enumeration of the avoiders.
