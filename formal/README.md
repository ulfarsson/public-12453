# `formal/` — the Lean 4 certificate

A machine-checked development, in Lean 4 with Mathlib, of the correctness half of the
paper *Protected tails and polynomial-time enumeration of permutations avoiding a direct sum of an increasing pattern and 231*
(`paper/av12453_polytime.tex`).  Two chains are certified end to end:

| `d` | class | literal recurrence | kernel algorithm |
|---|---|---|---|
| 1 | `Av(1342)` | `OneThreshold.av1342_count : W n [] = (avoiders n {beta 1}).card` | `OneThreshold.av1342_count_kernel : G n = (avoiders n {beta 1}).card` |
| 2 | `Av(12453)` | `TwoThreshold.av12453_count : H (n, 0) [] = (avoiders n {beta 2}).card` | `TwoThreshold.av12453_count_kernel : G (n, 0) = (avoiders n {beta 2}).card` |

`Av12453/Perm.lean` restates the two kernel theorems on Mathlib's model of a permutation, an
element of `Equiv.Perm (Fin n)`:

| `d` | kernel algorithm on `Equiv.Perm (Fin n)` |
|---|---|
| 1 | `OneThreshold.av1342_count_perm : G n = Fintype.card {σ : Equiv.Perm (Fin n) // PermAvoids σ beta1Perm}` |
| 2 | `TwoThreshold.av12453_count_perm : G (n, 0) = Fintype.card {σ : Equiv.Perm (Fin n) // PermAvoids σ beta2Perm}` |

`PermPatterns.avoiders n B` is the finset of permutations of `{0, …, n-1}` avoiding every
pattern of the finite basis `B`, its defining predicate being
`PermPatterns.AvoidsAll w B := ∀ τ ∈ B, Avoids w τ`; a one-pattern class is the singleton
basis `{τ}`, as in the statements above.  `Av12453.beta d = ι_d ⊕ 231`
(`beta 1 = [0,2,3,1] = 1342`, `beta 2 = [0,1,3,4,2] = 12453`, `0`-based;
`Av12453.beta_eq_directSum` proves the direct-sum form).

The `d = 2` kernel theorem certifies the *values* of the paper's unreduced `d = 2`
kernel recurrence (eq:K, eq:D, eq:G, eq:answer-G), i.e. the mathematical content of the
polynomial-time algorithm.  Not formalized: any complexity bound (the Lean `K` and `G`
are fuel-driven recursions, not the memoized sparse-row program), the two translation
quotients of the paper's Section 7 that give `O(N^7)`/`O(N^4)` for `12453`, and the
program `code/av12453_fast_rns.cpp` that produced the published `n = 150` and `n = 300`
data.  See `AUDIT_2026-09-05.md` for the trusted base a referee must check by eye.

Everything is `sorry`-free and uses only Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

## Modules

The package holds **two libraries**.  `PermPatterns` is the reusable, pattern-generic core
(namespace `PermPatterns`); `Av12453` is the paper-specific development (namespace
`Av12453`) and imports it.  Each is built in dependency order behind a root module that
imports all of its files: `PermPatterns.lean` imports the ten below, and `Av12453.lean`
imports `PermPatterns` and the twenty below.  The tables list them in dependency order.

### `PermPatterns` — the generic core

| module | lines | contents |
|---|---:|---|
| `PermPatterns/Word.lean` | 381 | words on `ℕ`, `IsWordOn`, `IsPermOf`, `isPermOf_iff`, `OrderIsomorphic` and its lemmas incl. `reverse`, `Picks` |
| `PermPatterns/Containment.lean` | 171 | `Contains`, `Avoids`, `AvoidsAll` over a finite basis, congruence under order isomorphism, `restrict` |
| `PermPatterns/Standardize.lean` | 189 | local `rank`, `standardize`, and their invariance properties |
| `PermPatterns/Patterns.lean` | 198 | `pat231`, `iota`, `orderIsomorphic_iota_iff`, `orderIsomorphic_triple_iff`, `contains_231_iff`, `IncrSubseq`, `IsTriggerAt`, `IsTrigger` |
| `PermPatterns/Sums.lean` | 204 | `directSum`, `skewSum`, their `IsPermOf` and `OrderIsomorphic` congruence lemmas, `contains_directSum_left`/`_right`, `reverse_directSum`, `skewSum_eq_reverse` |
| `PermPatterns/Decidable.lean` | 68 | `orderIsomorphic_iff_getD`, `contains_iff_sublists`, the `Decidable` instances for `IsPermOf`/ `OrderIsomorphic`/`Contains`/`Avoids`/`AvoidsAll` |
| `PermPatterns/Avoiders.lean` | 60 | `perms`, `mem_perms`, `avoiders n B`, `mem_avoiders`, `mem_avoiders_singleton`, `avoiders_empty`, `avoiders_anti` |
| `PermPatterns/Perm.lean` | 220 | the bridge to `Equiv.Perm (Fin n)`: `ofPerm`, `toPerm`, `permEquiv`, `PermContains`, `PermAvoids`, `permContains_iff_contains`, `card_avoiders_eq_fintypeCard` |
| `PermPatterns/Symmetry.lean` | 350 | `complement`, `inverse`, `permReverse`, `permComplement`, the three containment transports, `card_avoiders_reverse`/`_complement`/`_inverse` |
| `PermPatterns/FirstLetter.lean` | 352 | the first-letter lemma for `Av(231)` (`lem:first-letter`) |

### `Av12453` — the paper-specific development

| component | module | lines | headline results (paper) |
|---|---|---:|---|
| 1–2 | `Av12453/Basic.lean` | 215 | `beta`, `beta_eq_directSum`, `contains_beta_iff`, `contains_12453_iff` |
| 1–2 | `Av12453/Trigger.lean` | 282 | `avoids_beta_iff_forall_trigger` — the trigger lemma (`lem:trigger`) |
| 3a | `Av12453/OneThreshold/Defs.lean` | 1249 | the `d = 1` scan, the state `(p, L)`, the literal recurrence `W` (`eq:W`) |
| 3a | `…/OneThreshold/Invariant.lean` | 358 | (A) the separation invariant (`lem:1342-separators`) |
| 3a | `…/OneThreshold/Semantics.lean` | 405 | (B) deferred letters have no completion; (C) legal complete words avoid `1342` |
| 3a | `…/OneThreshold/Counting.lean` | 455 | (D) `A_eq_W`, and **`av1342_count`** (`thm:literal` at `d = 1`) |
| 4a | `…/OneThreshold/Kernel.lean` | 299 | `K`, `D`, `G` and `K_zero`/`K_succ_eq`/`D_one`/`D_succ`/`G_eq` (`eq:scalar-K`–`eq:scalar-G`) |
| 4a | `…/OneThreshold/KernelSupport.lean` | 297 | `K_support_eq` (`eq:scalar-support`), `K_diag_eq_catalan`, range extension |
| 4a | `…/OneThreshold/KernelFactor.lean` | 232 | `W_factor` (`eq:scalar-factorization`) |
| 4a | `…/OneThreshold/KernelCount.lean` | 252 | `G_eq_W`, **`av1342_count_kernel`** (`thm:scalar-algorithm`, correctness half) |
| 3b | `…/TwoThreshold/Thresholds.lean` | 751 | the threshold API `b₁ < b₂`, bands, control, `lem:least-trigger-frontier` |
| 3b | `…/TwoThreshold/Defs.lean` | 1254 | the `d = 2` scan and the literal recurrence `H` (`eq:H`, `eq:initial-terminal`) |
| 3b | `…/TwoThreshold/Invariant.lean` | 457 | (A) the separation invariant at `d = 2` (`cor:separators`) |
| 3b | `…/TwoThreshold/Semantics.lean` | 402 | (B) and (C) at `d = 2` |
| 3b | `…/TwoThreshold/Counting.lean` | 591 | (D) `A_eq_H`, and **`av12453_count`** (`thm:literal` at `d = 2`) |
| 4b | `…/TwoThreshold/Kernel.lean` | 455 | `ctrls`/`S`, `K`, `D`, `G` and their equations (`eq:K`, `eq:D`, `eq:G`) |
| 4b | `…/TwoThreshold/KernelSupport.lean` | 366 | `K_eq_zero_of_mass_lt`, `K_support` (`lem:support`, `eq:support`), range extension |
| 4b | `…/TwoThreshold/KernelFactor.lean` | 436 | `H_factor` (`eq:factorization`), the layer identity `K_ℓ((0,q),(0,s)) = K^{(1)}_ℓ(q,s)` |
| 4b | `…/TwoThreshold/KernelCount.lean` | 312 | `G_eq_H`, **`av12453_count_kernel`** (`eq:answer-G` at `d = 2`) |
| 4a, 4b | `Av12453/Perm.lean` | 110 | `beta1Perm`, `beta2Perm`, **`av1342_count_perm`**, **`av12453_count_perm`** — the two kernel theorems on `Equiv.Perm (Fin n)` |

11 371 lines of Lean in the thirty modules of the two libraries — 2 193 in `PermPatterns`
and 9 178 in `Av12453` — plus the two root modules `PermPatterns.lean` (110 lines) and
`Av12453.lean` (21 lines), which only import, and 63 lines of `Av12453/Axioms.lean`, which
belongs to neither library: **11 565** lines of Lean in all.

### Imports

`PermPatterns` is import-minimised: every module lists exactly the Mathlib modules it needs,
and none of them imports the root module `Mathlib` or the tactic bundle `Mathlib.Tactic`.
The whole list is `Mathlib.Data.Finset.Card`, `.Dedup` and `.Insert`,
`Mathlib.Data.Fintype.Perm`, `Mathlib.Data.List.GetD`, `.NodupEquivFin`, `.Permutation` and
`.Sublists`, and the two tactics `Mathlib.Tactic.FinCases` and `Mathlib.Tactic.IntervalCases`
(`Sums.lean`, `Symmetry.lean`, `FirstLetter.lean` and the root module import only siblings).
`import PermPatterns` therefore loads **2340** modules, 607 of them Mathlib's, instead of the
**10509** (8312 Mathlib) that a wholesale `import Mathlib` pulls in.  `Av12453` is
deliberately *not* minimised: `Av12453/Basic.lean` imports `Mathlib` and every module of that
library is downstream of it, so the paper-specific development is unaffected.

## Reports and briefs

The per-component development briefs and reports that guided the development were removed on
2026-09-06 (they remain in git history).  The closing assessment of the whole `d = 2`
certificate, the trusted base a referee must check by eye, and the audit findings are in
`AUDIT_2026-09-05.md`.

## Building and auditing

```sh
export PATH="$HOME/.elan/bin:$PATH"
cd formal/Av12453
lake build                              # both libraries; ~9 min cold, seconds warm
lake build PermPatterns                 # the generic core alone
lake env lean Av12453/Axioms.lean       # axiom sweep over both libraries
sh ../check.sh                          # build, sweep, sweep coverage and a token scan
```

`lake build` must finish with no errors and no warnings.  `Axioms.lean` is **self-checking**:
instead of reading a hand-maintained list of modules it discovers, from the environment,
every imported module whose name begins with `PermPatterns` or with `Av12453`, and it aborts
if either prefix matches no module — so a module that is added, renamed or moved between the
two libraries cannot silently drop out of the check.  It walks *every* constant declared in
those modules — including `private` declarations and auto-generated constants; `example`s
declare no constant and are outside the sweep, but no theorem can depend on them — reports
the axioms each depends on, and **throws an error** if any depends on `sorryAx` or on an
axiom outside `{propext, Classical.choice, Quot.sound}`.  It ends with a
`checked N declarations in […]` line; exit code `0` is the audit passing.  On the current
tree it reports **`checked 1594 declarations`** over **32** modules — the thirty library
modules and the two roots.

`check.sh` runs the build and the sweep together, and adds the one check the sweep cannot
make about itself: it compares the number of modules the sweep reports with the number of
`.lean` files in the tree, so a module that no root imports — and that the sweep would
therefore never see — fails the check; it prints `sweep covered all 32 modules` when they
agree.  It also greps the sources for `sorry`,
`native_decide` and `admit`.  The same sweep runs in CI as the named step *Axiom and sorry
sweep* in `.github/workflows/lean_action_ci.yml`.

Never run `lake update` or `lake exe cache get`, and do not touch `.lake/packages`: the
toolchain (`lean-toolchain`) and the Mathlib revision (`lake-manifest.json`) are pinned.

To re-derive the numbers rather than trust them, the `#eval`/`decide` blocks at the end of
each `Kernel*.lean` print the first terms of `|Av_n(1342)|` and `|Av_n(12453)|` from the
kernel tables; `OneThreshold/Counting.lean` and `TwoThreshold/Counting.lean` compare them
with brute-force enumeration of the avoiders.

## License

Apache-2.0.  The `LICENSE` file every source header cites is at the package root,
`formal/Av12453/LICENSE`.
