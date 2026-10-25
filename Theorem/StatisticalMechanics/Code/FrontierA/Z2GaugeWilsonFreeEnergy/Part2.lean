/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonFreeEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualEquiv.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonSupport
import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonFreeEnergy.Part2
open scoped BigOperators symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


theorem multibondIsingPartition_eq_Z_neg_one
    (ends : P → V × V) (J : P → Real) :
    multibondIsingPartition ends J =
      StatMech.Ising.Z (-1) (multibondIsingAction ends J) := by
  simp [multibondIsingPartition, multibondIsingWeight,
    StatMech.Ising.Z, multibondIsingAction]


theorem multibondIsingAction_twist_sub_abs_le
    (ends : P → V × V) (J : P → Real) (D : Finset P) (s : V → Bool) :
    |multibondIsingAction ends J s -
        multibondIsingAction ends (multibondTwistCoupling J D) s| ≤
      2 * ∑ p ∈ D, |J p| := by
  classical
  unfold multibondIsingAction
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ p : P, (
        (J p * if s (ends p).1 = s (ends p).2 then 1 else -1) -
          multibondTwistCoupling J D p *
            (if s (ends p).1 = s (ends p).2 then 1 else -1))|
        ≤ ∑ p : P, |(
            (J p * if s (ends p).1 = s (ends p).2 then 1 else -1) -
              multibondTwistCoupling J D p *
                (if s (ends p).1 = s (ends p).2 then 1 else -1))| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p : P, if p ∈ D then 2 * |J p| else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p ∈ D <;>
        by_cases hs : s (ends p).1 = s (ends p).2 <;>
        simp [multibondTwistCoupling, hp, hs] <;>
        ring_nf <;> simp [abs_mul]
    _ = 2 * ∑ p ∈ D, |J p| := by
      rw [← Finset.sum_filter]
      simp only [subset_univ, filter_mem_eq_of_subset]
      rw [← Finset.mul_sum]


end
end StatMech.FrontierA
