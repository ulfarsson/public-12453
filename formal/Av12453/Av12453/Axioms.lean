/-
Scratch axiom check for components 1, 2, 3a, 4a, 3b and 4b.

NOT part of the library: `Av12453.lean` does not import this file, and the Lake
`lean_lib Av12453` target does not glob it.  Run it with

    lake env lean Av12453/Axioms.lean

The `#axioms_of` command below walks *every* constant declared in the twenty
modules `Av12453.Basic`, `Av12453.Trigger`, `Av12453.FirstLetter`,
`Av12453.OneThreshold.Defs`, `Av12453.OneThreshold.Invariant`,
`Av12453.OneThreshold.Semantics`, `Av12453.OneThreshold.Counting`,
`Av12453.OneThreshold.Kernel`, `Av12453.OneThreshold.KernelSupport`,
`Av12453.OneThreshold.KernelFactor`, `Av12453.OneThreshold.KernelCount`,
`Av12453.TwoThreshold.Thresholds`, `Av12453.TwoThreshold.Defs`,
`Av12453.TwoThreshold.Invariant`, `Av12453.TwoThreshold.Semantics`,
`Av12453.TwoThreshold.Counting`, `Av12453.TwoThreshold.Kernel`,
`Av12453.TwoThreshold.KernelSupport`, `Av12453.TwoThreshold.KernelFactor`,
`Av12453.TwoThreshold.KernelCount`
-- including
`private` declarations and every auto-generated declaration (`example`s declare no
constant and are outside the sweep; no theorem can depend on them)
(structure projections, equation lemmas, compiler stages) -- and reports the axioms it depends
on.  It throws an
error if any of them depends on `sorryAx` or on any axiom outside
`{propext, Classical.choice, Quot.sound}`.
-/
import Av12453.Basic
import Av12453.Trigger
import Av12453.FirstLetter
import Av12453.OneThreshold.Defs
import Av12453.OneThreshold.Invariant
import Av12453.OneThreshold.Semantics
import Av12453.OneThreshold.Counting
import Av12453.OneThreshold.Kernel
import Av12453.OneThreshold.KernelSupport
import Av12453.OneThreshold.KernelFactor
import Av12453.OneThreshold.KernelCount
import Av12453.TwoThreshold.Thresholds
import Av12453.TwoThreshold.Defs
import Av12453.TwoThreshold.Invariant
import Av12453.TwoThreshold.Semantics
import Av12453.TwoThreshold.Counting
import Av12453.TwoThreshold.Kernel
import Av12453.TwoThreshold.KernelSupport
import Av12453.TwoThreshold.KernelFactor
import Av12453.TwoThreshold.KernelCount

open Lean Elab Command

/-- Print, for every constant declared in the listed modules, the axioms it uses. -/
syntax (name := axiomsOf) "#axioms_of " ident+ : command

@[command_elab axiomsOf]
def elabAxiomsOf : CommandElab := fun stx => do
  let mods : Array Name := stx[1].getArgs.map (·.getId)
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
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

#axioms_of Av12453.Basic Av12453.Trigger Av12453.FirstLetter
  Av12453.OneThreshold.Defs Av12453.OneThreshold.Invariant
  Av12453.OneThreshold.Semantics Av12453.OneThreshold.Counting
  Av12453.OneThreshold.Kernel Av12453.OneThreshold.KernelSupport
  Av12453.OneThreshold.KernelFactor Av12453.OneThreshold.KernelCount
  Av12453.TwoThreshold.Thresholds Av12453.TwoThreshold.Defs
  Av12453.TwoThreshold.Invariant Av12453.TwoThreshold.Semantics
  Av12453.TwoThreshold.Counting
  Av12453.TwoThreshold.Kernel Av12453.TwoThreshold.KernelSupport
  Av12453.TwoThreshold.KernelFactor Av12453.TwoThreshold.KernelCount
