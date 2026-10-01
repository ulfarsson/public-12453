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
kernel recurrence (eq:K, eq:G, eq:answer-G), i.e. the mathematical content of the
polynomial-time algorithm.  Not formalized: any complexity bound (the Lean `K` and `G`
are fuel-driven recursions, not the memoized sparse-row program), the two translation
quotients of the paper's Section 7 that give `O(N^7)`/`O(N^4)` for `12453`, and the
programs that produced the published data (`code/av12453_fast_rns.cpp` for the `n = 150`
certificate, the engine in `code/av12453_n300/` for the `n = 300` series).  What a reader
must trust is described under *What must be trusted* below.

The two libraries and `Solution.lean` are `sorry`-free, and every theorem of the libraries
uses only Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`); the
comparator checks the same of the four theorems of `Solution.lean`.  The only `sorry`s are
the four placeholders of `Challenge.lean`, which state the theorems that the comparator
checks `Solution.lean` against (see below).

## The statement file (Palomar format)

`Challenge.lean` is the whole statement surface: about 180 lines that import only Mathlib
and contain pattern containment for permutations of `Fin n` (`PermPatterns.PermContains`),
the patterns `1342` and `12453` as products of transpositions, and the definitions of `W`,
`H`, `K` and `G` for `d = 1, 2`, followed by the four headline theorems

| theorem | statement |
|---|---|
| `Av12453.count_1342_literal` | `OneThreshold.W n [] = Nat.card {σ : Equiv.Perm (Fin n) // ¬ PermContains σ pattern1342}` |
| `Av12453.count_1342_kernel` | `OneThreshold.G n = Nat.card {σ … // ¬ PermContains σ pattern1342}` |
| `Av12453.count_12453_literal` | `TwoThreshold.H (n, 0) [] = Nat.card {σ … // ¬ PermContains σ pattern12453}` |
| `Av12453.count_12453_kernel` | `TwoThreshold.G (n, 0) = Nat.card {σ … // ¬ PermContains σ pattern12453}` |

stated with `sorry`.  `Solution.lean` proves them from the development (without importing
`Challenge.lean`), `comparator.json` names them and the permitted axioms, and
`formalization.yaml` is the registry metadata.  `bash ../comparator.sh` runs `lake
comparator`, which checks that each theorem of `Solution.lean` proves exactly the statement
of `Challenge.lean` (with every definition it uses identical), uses only the permitted
axioms, and is accepted by Lean's kernel and by the independent kernels nanoda and con-ron;
it ends with `Your solution is okay!`.  A reader who wants to know what is proved needs to
read `Challenge.lean` only.

## Modules

The package holds **two libraries**.  `PermPatterns` is the reusable, pattern-generic core
(namespace `PermPatterns`); `Av12453` is the paper-specific development (namespace
`Av12453`) and imports it.  Each is built in dependency order behind a root module that
imports all of its files: `PermPatterns.lean` imports the ten below, and `Av12453.lean`
imports `PermPatterns` and the twenty below.  The tables list them in dependency order.

### `PermPatterns` — the generic core

| module | lines | contents |
|---|---:|---|
| `PermPatterns/Word.lean` | 385 | words on `ℕ`, `IsWordOn`, `IsPermOf`, `isPermOf_iff`, `OrderIsomorphic` and its lemmas incl. `reverse`, `Picks` |
| `PermPatterns/Containment.lean` | 175 | `Contains`, `Avoids`, `AvoidsAll` over a finite basis, congruence under order isomorphism, `restrict` |
| `PermPatterns/Standardize.lean` | 194 | local `rank`, `standardize`, and their invariance properties |
| `PermPatterns/Patterns.lean` | 202 | `pat231`, `iota`, `orderIsomorphic_iota_iff`, `orderIsomorphic_triple_iff`, `contains_231_iff`, `IncrSubseq`, `IsTriggerAt`, `IsTrigger` |
| `PermPatterns/Sums.lean` | 208 | `directSum`, `skewSum`, their `IsPermOf` and `OrderIsomorphic` congruence lemmas, `contains_directSum_left`/`_right`, `reverse_directSum`, `skewSum_eq_reverse` |
| `PermPatterns/Decidable.lean` | 72 | `orderIsomorphic_iff_getD`, `contains_iff_sublists`, the `Decidable` instances for `IsPermOf`/ `OrderIsomorphic`/`Contains`/`Avoids`/`AvoidsAll` |
| `PermPatterns/Avoiders.lean` | 64 | `perms`, `mem_perms`, `avoiders n B`, `mem_avoiders`, `mem_avoiders_singleton`, `avoiders_empty`, `avoiders_anti` |
| `PermPatterns/Perm.lean` | 224 | the bridge to `Equiv.Perm (Fin n)`: `ofPerm`, `toPerm`, `permEquiv`, `PermContains`, `PermAvoids`, `permContains_iff_contains`, `card_avoiders_eq_fintypeCard` |
| `PermPatterns/Symmetry.lean` | 354 | `complement`, `inverse`, `permReverse`, `permComplement`, the three containment transports, `card_avoiders_reverse`/`_complement`/`_inverse` |
| `PermPatterns/FirstLetter.lean` | 356 | the first-letter lemma for `Av(231)` (`lem:first-letter`) |

### `Av12453` — the paper-specific development

| module | lines | headline results (paper) |
|---|---:|---|
| `Av12453/Basic.lean` | 219 | `beta`, `beta_eq_directSum`, `contains_beta_iff`, `contains_12453_iff` |
| `Av12453/Trigger.lean` | 285 | `avoids_beta_iff_forall_trigger` — the trigger lemma (`lem:trigger`) |
| `Av12453/OneThreshold/Defs.lean` | 1255 | the `d = 1` scan, the state `(p, L)`, the literal recurrence `W` (`eq:W`) |
| `…/OneThreshold/Invariant.lean` | 359 | the separation invariant (`lem:separators`) |
| `…/OneThreshold/Semantics.lean` | 407 | deferred letters have no completion; legal complete words avoid `1342` |
| `…/OneThreshold/Counting.lean` | 462 | `A_eq_W`, and **`av1342_count`** (`thm:literal` at `d = 1`) |
| `…/OneThreshold/Kernel.lean` | 335 | `K`, `D`, `G` and `K_zero`/`K_succ_eq`/`D_one`/`D_succ`/`G_eq` (`eq:scalar-K`–`eq:scalar-G`) |
| `…/OneThreshold/KernelSupport.lean` | 302 | `K_support_eq` (`eq:scalar-support`), `K_diag_eq_catalan`, range extension |
| `…/OneThreshold/KernelFactor.lean` | 225 | `W_factor` (`eq:scalar-factorization`) |
| `…/OneThreshold/KernelCount.lean` | 287 | `G_eq_W`, **`av1342_count_kernel`** (`thm:scalar-algorithm`, correctness half) |
| `…/TwoThreshold/Thresholds.lean` | 755 | the threshold API `b₁ < b₂`, bands, control, `eq:bd-q` |
| `…/TwoThreshold/Defs.lean` | 1266 | the `d = 2` scan and the literal recurrence `H` (`eq:H`, `eq:initial-terminal`) |
| `…/TwoThreshold/Invariant.lean` | 459 | the separation invariant at `d = 2` (`lem:separators`, `cor:separators`) |
| `…/TwoThreshold/Semantics.lean` | 400 | the same two statements at `d = 2` |
| `…/TwoThreshold/Counting.lean` | 598 | `A_eq_H`, and **`av12453_count`** (`thm:literal` at `d = 2`) |
| `…/TwoThreshold/Kernel.lean` | 469 | `ctrls`/`S`, `K`, `D`, `G` and their equations (`eq:K`, `eq:G`) |
| `…/TwoThreshold/KernelSupport.lean` | 372 | `K_eq_zero_of_mass_lt`, `K_support` (`lem:support`, `eq:support`), range extension |
| `…/TwoThreshold/KernelFactor.lean` | 442 | `H_factor` (`eq:factorization`), the layer identity `K_ℓ((0,q),(0,s)) = K^{(1)}_ℓ(q,s)` |
| `…/TwoThreshold/KernelCount.lean` | 308 | `G_eq_H`, **`av12453_count_kernel`** (`eq:answer-G` at `d = 2`) |
| `Av12453/Perm.lean` | 119 | `beta1Perm`, `beta2Perm`, **`av1342_count_perm`**, **`av12453_count_perm`** — the two kernel theorems on `Equiv.Perm (Fin n)` |

11 558 lines of Lean in the thirty modules of the two libraries — 2 234 in `PermPatterns`
and 9 324 in `Av12453` — plus the two root modules `PermPatterns.lean` (114 lines) and
`Av12453.lean` (23 lines), which only import, and 96 lines of `Av12453/Axioms.lean`, which
belongs to neither library: **11 791** lines of Lean in all, besides `Challenge.lean` (180 lines)
and `Solution.lean` (62 lines).

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

## What must be trusted

To know what is proved, read `Challenge.lean`.  It imports only Mathlib and contains the four
statements and every definition they use: pattern containment `PermContains` for
`Equiv.Perm (Fin n)`, the patterns `1342` and `12453` as products of transpositions, and the
recurrences `W`, `H`, `K` and `G` for `d = 1, 2`.  Comparing these definitions with the
paper's displays (`eq:W` and `eq:W-boundary`, `eq:H` with `H_0(∅) = 1`,
`eq:scalar-K`–`eq:scalar-G`, `eq:K`–`eq:G`) takes three
facts, which Appendix B of the paper explains.  The recurrences are written with a recursion
bound, and the development proves that every sufficient bound gives the same value.  In the
kernel recurrences every sum over intermediate or terminal controls is restricted to the
controls of mass at most that of the source control, which the paper's Lemmas 2.17 and 6.1
show loses nothing.  The terms of the split sums with `a = 0` or `b = 0` are written as one
endpoint term, with a case distinction on whether the head has size one
(`if ℓ = 0 then … else 2 * …`); the development's restated equations call it `D` in the
kernel recurrences and `Eend` in those of `W` and `H`.  No natural-number subtraction in the definitions truncates: each
is guarded by its range (for example `h < p₀` in `p₁ + p₀ - 1 - h`).

Beyond `Challenge.lean`, the trusted base is Lean's kernel, the Mathlib definitions that
`Challenge.lean` uses (`Equiv.Perm`, `Fin`, `Nat.card`, finite sums), and the pinned
toolchain.  The proofs, `Solution.lean` and the two libraries need not be read:
`comparator.sh` checks that each theorem of `Solution.lean` has exactly the statement of
`Challenge.lean`, with every definition it uses identical, that it uses only the three
standard axioms, and that Lean's kernel and the independent kernels nanoda and con-ron accept
it.

## Building and auditing

```sh
export PATH="$HOME/.elan/bin:$PATH"
cd formal/Av12453
lake exe cache get                      # once: Mathlib's prebuilt files
lake build                              # both libraries and Challenge/Solution; seconds warm
lake build PermPatterns                 # the generic core alone
lake env lean Av12453/Axioms.lean       # axiom sweep over both libraries
bash ../check.sh                        # build, sweep, sweep coverage and a token scan
bash ../comparator.sh                   # Palomar's check of Solution against Challenge
```

Every file uses Lean's module system (`module`, `public import`, an exposed public
section), as Palomar requires.  The toolchain is pinned to Lean and Mathlib `v4.35.0-rc2`;
the same sources also build unchanged on Lean `v4.33.1` with Mathlib `0df444a3`, the
default environment of Prove2Me.

`lake build PermPatterns Av12453 Solution` must finish with no errors and no warnings;
`lake build Challenge` (and so a plain `lake build`, whose default targets include it) gives
exactly four warnings, `declaration uses 'sorry'`, one for each placeholder of
`Challenge.lean`.  `Axioms.lean` is **self-checking**:
instead of reading a hand-maintained list of modules it discovers, from the environment,
every imported module whose name begins with `PermPatterns` or with `Av12453`, and it aborts
if either prefix matches no module — so a module that is added, renamed or moved between the
two libraries cannot silently drop out of the check.  It walks *every* constant declared in
those modules — including `private` declarations and auto-generated constants; `example`s
declare no constant and are outside the sweep, but no theorem can depend on them — reports
the axioms each depends on, and **throws an error** if any depends on `sorryAx` or on an
axiom outside `{propext, Classical.choice, Quot.sound}`.  It ends with a
`checked N declarations in […]` line; exit code `0` is the audit passing.  On the current
tree it reports **`checked 1599 declarations`** over **32** modules — the thirty library
modules and the two roots.

`check.sh` runs the build and the sweep together, and adds the one check the sweep cannot
make about itself: it compares the number of modules the sweep reports with the number of
`.lean` files in the tree, so a module that no root imports — and that the sweep would
therefore never see — fails the check; it prints `sweep covered all 32 modules` when they
agree.  It also greps the sources of the two libraries for `sorry`, `native_decide` and
`admit`; `Challenge.lean` is not scanned, since its four placeholders are `sorry` by design,
and `Solution.lean` is covered by its warning-free build and by the comparator.  In the
public repository, the workflow `.github/workflows/lean.yml` runs `check.sh` and
`comparator.sh` on GitHub's servers on every push.

Never run `lake update`, and do not touch `.lake/packages`: the toolchain
(`lean-toolchain`) and the Mathlib revision (`lake-manifest.json`) are pinned.
`lake exe cache get` only downloads Mathlib's build for the pinned revision.

To re-derive the numbers rather than trust them, the `#eval`/`decide` blocks at the end of
each `Kernel*.lean` print the first terms of `|Av_n(1342)|` and `|Av_n(12453)|` from the
kernel tables; `OneThreshold/Counting.lean` and `TwoThreshold/Counting.lean` compare them
with brute-force enumeration of the avoiders.

## License

Apache-2.0.  The `LICENSE` file every source header cites is at the package root,
`formal/Av12453/LICENSE`.
