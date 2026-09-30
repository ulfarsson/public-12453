# Av12453 — Lean 4 formalization

This Lake package holds the machine-checked part of *Protected tails and polynomial-time
enumeration of permutations avoiding a direct sum of an increasing pattern and 231*.  It
builds two libraries from one source tree.

## The two libraries

### `PermPatterns` — the reusable core

Generic classical permutation-pattern material, with no reference to the paper's pattern
family beyond `231` and `ι_d`:

| module | contents |
|---|---|
| `PermPatterns.Word` | words on `ℕ`, `IsWordOn`, `IsPermOf`, `OrderIsomorphic`, `Picks` |
| `PermPatterns.Containment` | `Contains`, `Avoids`, `AvoidsAll`, the restriction `restrict` |
| `PermPatterns.Standardize` | the local rank `rank` and the standardization `standardize` |
| `PermPatterns.Patterns` | `pat231`, `iota`, `IncrSubseq`, `IsTriggerAt`, `IsTrigger` |
| `PermPatterns.Sums` | the direct sum `directSum` and the skew sum `skewSum` |
| `PermPatterns.Decidable` | decidability of `IsPermOf`, `OrderIsomorphic`, containment, avoidance |
| `PermPatterns.Avoiders` | the finite sets `perms n` and `avoiders n B` |
| `PermPatterns.Perm` | the bridge to `Equiv.Perm (Fin n)`: `ofPerm`, `toPerm`, `permEquiv` |
| `PermPatterns.Symmetry` | the reverse, complement and inverse, and Wilf equivalence |
| `PermPatterns.FirstLetter` | the first-letter lemma for `Av(231)` |

The root module `PermPatterns.lean` imports all of these and carries the translation table
between the usual `1`-based notation and the `0`-based one used here.

### `Av12453` — the paper-specific development

Everything about `β_d = ι_d ⊕ 231`, built on top of `PermPatterns`:

| module | contents |
|---|---|
| `Av12453.Basic` | the pattern `beta d` and the index forms of `β_d`- and `12453`-containment |
| `Av12453.Trigger` | Lemma 2.1, the trigger lemma |
| `Av12453.Perm` | the two headline counts restated on `Equiv.Perm (Fin n)` |
| `Av12453.OneThreshold.*` | the one-threshold scan and kernel for `Av(1342)` (`d = 1`) |
| `Av12453.TwoThreshold.*` | the two-threshold scan and kernel for `Av(12453)` (`d = 2`) |

The four headline theorems are `Av12453.OneThreshold.av1342_count`,
`Av12453.OneThreshold.av1342_count_kernel`, `Av12453.TwoThreshold.av12453_count` and
`Av12453.TwoThreshold.av12453_count_kernel`.  `Av12453.Perm` restates the two kernel
theorems on `Equiv.Perm (Fin n)` as `Av12453.OneThreshold.av1342_count_perm` and
`Av12453.TwoThreshold.av12453_count_perm`.

`Av12453.Axioms` is not part of either library: no root module imports it and no
`lean_lib` target globs it.

## Imports

`PermPatterns` is import-minimised: every module lists exactly the Mathlib modules it needs,
and no module imports the root module `Mathlib` or the tactic bundle `Mathlib.Tactic`.
`import PermPatterns` pulls in 607 of Mathlib's 8312 modules (2340 modules in all, counting
the Lean, `Std`, `Batteries` and `Aesop` layers below Mathlib).  Each import was checked to
be individually necessary: dropping any one of them breaks `lake build PermPatterns`.

`Av12453` is deliberately *not* minimised.  `Av12453.Basic` imports the root module
`Mathlib`, and every module of that library is downstream of it, so the paper-specific
development sees all of Mathlib.

## Building

Mathlib is pinned in `lake-manifest.json`; the toolchain is in `lean-toolchain`.

```sh
lake build                 # both libraries
lake build PermPatterns    # the reusable core alone
```

## The axiom sweep

```sh
lake env lean Av12453/Axioms.lean
```

This walks every constant — `private` and auto-generated ones included — declared in every
imported module whose name begins with `PermPatterns` or `Av12453`, and reports the axioms it
depends on.  The sweep discovers its own module list from the environment, so a new or moved
module cannot silently drop out of it; it fails if either prefix matches no module, and it
fails if any constant depends on `sorryAx` or on anything outside
`{propext, Classical.choice, Quot.sound}`.

`../check.sh` runs the whole certificate check: a warning-free `lake build`, the axiom sweep,
and a scan for `sorry`, `native_decide` and `admit` in both libraries.  It ends with
`CERTIFICATE CHECK PASSED`.

## See also

* `../README.md` — how the formalization relates to the paper, component by component.
* `../AUDIT_2026-09-05.md` — the audit of the formalization against the manuscript.
