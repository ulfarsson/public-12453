/-
Axiom check for the two libraries `PermPatterns` and `Av12453`.

NOT part of either library: neither `PermPatterns.lean` nor `Av12453.lean` imports this file,
and the Lake `lean_lib` targets do not glob it.  Run it with

    lake env lean Av12453/Axioms.lean

The `#axioms_sweep` command below is *self-checking*: rather than reading a hand-maintained
list of modules, it sweeps **every** imported module whose name begins with `PermPatterns` or
with `Av12453` (except this file itself), so a module that is added, renamed or moved between
the two libraries can never silently drop out of the check.  It aborts if either prefix
matches no imported module, and it prints the list of modules it swept.

For every constant declared in those modules, including `private` declarations and every
auto-generated declaration (structure projections, equation lemmas, compiler stages), it
reports the axioms the constant depends on, and it throws an error if any of them depends on
`sorryAx` or on any axiom outside `{propext, Classical.choice, Quot.sound}`.  An `example`
declares no constant, so it is outside the sweep, and no theorem can depend on it.
-/
module

public import PermPatterns
public import Av12453
import all PermPatterns.Word
import all PermPatterns.Containment
import all PermPatterns.Standardize
import all PermPatterns.Patterns
import all PermPatterns.Sums
import all PermPatterns.Decidable
import all PermPatterns.Avoiders
import all PermPatterns.Perm
import all PermPatterns.Symmetry
import all PermPatterns.FirstLetter
import all Av12453.Basic
import all Av12453.Trigger
import all Av12453.OneThreshold.Defs
import all Av12453.OneThreshold.Invariant
import all Av12453.OneThreshold.Semantics
import all Av12453.OneThreshold.Counting
import all Av12453.OneThreshold.Kernel
import all Av12453.OneThreshold.KernelSupport
import all Av12453.OneThreshold.KernelFactor
import all Av12453.OneThreshold.KernelCount
import all Av12453.TwoThreshold.Thresholds
import all Av12453.TwoThreshold.Defs
import all Av12453.TwoThreshold.Invariant
import all Av12453.TwoThreshold.Semantics
import all Av12453.TwoThreshold.Counting
import all Av12453.TwoThreshold.Kernel
import all Av12453.TwoThreshold.KernelSupport
import all Av12453.TwoThreshold.KernelFactor
import all Av12453.TwoThreshold.KernelCount
import all Av12453.Perm
public meta import Lean.Elab.Command

open Lean Elab Command

/-- Sweep every imported `PermPatterns.*` and `Av12453.*` module and print, for every
constant declared in them, the axioms it uses. -/
syntax (name := axiomsSweep) "#axioms_sweep" : command

@[command_elab axiomsSweep]
public meta def elabAxiomsSweep : CommandElab := fun _ => do
  let env ← getEnv
  let prefixes : Array Name := #[`PermPatterns, `Av12453]
  let self : Name := `Av12453.Axioms
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut mods : Array Name := #[]
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if m != self && prefixes.any (fun p => p.isPrefixOf m) then
      mods := mods.push m
  for p in prefixes do
    if !mods.any (fun m => p.isPrefixOf m) then
      throwError m!"EMPTY SWEEP: no imported module has the prefix '{p}'"
  logInfo m!"sweeping {mods.size} modules: {mods.toList}"
  let mut bad : Array Name := #[]
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if !mods.contains env.header.moduleNames[i]! then continue
    for c in env.header.moduleData[i]!.constNames do
      let axs : Array Name ← collectAxioms c
      count := count + 1
      if axs.isEmpty then
        logInfo m!"'{c}' does not depend on any axioms"
      else
        logInfo m!"'{c}' depends on axioms: {(axs.qsort Name.lt).toList}"
      for a in axs do
        if !allowed.contains a then
          bad := bad.push c
  logInfo m!"checked {count} declarations in {mods.toList}"
  if !bad.isEmpty then
    throwError m!"NON-STANDARD AXIOM(S) used by: {bad.toList}"

#axioms_sweep
