/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldMacroArrayAssembly.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldArrayClosure.Part5
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

def PeriodicPlaneEmbedding.NormalBoundaryBandFamily.AlignedMarginSchedule
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (verticalRequirement horizontalRequirement : Nat → Nat) : Prop :=
  ∃ horizontal vertical : Nat → Nat,
    Tendsto horizontal atTop atTop ∧ Tendsto vertical atTop atTop ∧
    (∀ n, verticalRequirement (horizontal n) ≤ vertical n) ∧
    (∀ n, horizontalRequirement (vertical n) ≤ horizontal (n + 1)) ∧
    (∀ n, (family.radiusLeft (horizontal n) : Int) +
      family.baseLeft 1 ≤ family.baseBottom 1 + vertical n) ∧
    (∀ n, (family.radiusRight (horizontal n) : Int) +
      family.baseRight 1 ≤ family.baseBottom 1 + vertical n) ∧
    (∀ n, (family.radiusLeft (horizontal n) : Int) +
      family.baseTop 1 ≤ family.baseLeft 1 + vertical n) ∧
    (∀ n, (family.radiusRight (horizontal n) : Int) +
      family.baseTop 1 ≤ family.baseRight 1 + vertical n) ∧
    (∀ n, (family.radiusBottom (vertical n) : Int) +
      family.baseBottom 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧
    (∀ n, (family.radiusTop (vertical n) : Int) +
      family.baseTop 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧
    (∀ n, (family.radiusBottom (vertical n) : Int) +
      family.baseRight 0 ≤ family.baseBottom 0 + horizontal (n + 1)) ∧
    (∀ n, (family.radiusTop (vertical n) : Int) +
      family.baseRight 0 ≤ family.baseTop 0 + horizontal (n + 1))

end StatMech.FK.PeriodicPlanar
