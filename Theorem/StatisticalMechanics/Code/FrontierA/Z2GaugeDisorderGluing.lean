/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionThermodynamic.Part3
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.flexible false
set_option linter.style.multiGoal false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


theorem multibondIsingAction_coupling_sub_abs_le
    (ends : P → V × V) (J J' : P → Real) (s : V → Bool) :
    |multibondIsingAction ends J s - multibondIsingAction ends J' s| ≤
      ∑ p : P, |J p - J' p| := by
  classical
  unfold multibondIsingAction
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ p : P, (
        (J p * if s (ends p).1 = s (ends p).2 then 1 else -1) -
          J' p * if s (ends p).1 = s (ends p).2 then 1 else -1)|
        ≤ ∑ p : P, |(
            (J p * if s (ends p).1 = s (ends p).2 then 1 else -1) -
              J' p * if s (ends p).1 = s (ends p).2 then 1 else -1)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p : P, |J p - J' p| := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hs : s (ends p).1 = s (ends p).2
      · simp [hs]
      · simp [hs]
        have hneg : -J p + J' p = -(J p - J' p) := by ring
        rw [hneg, abs_neg]


theorem multibondIsing_logPartition_coupling_sub_abs_le
    (ends : P → V × V) (J J' : P → Real) :
    |Real.log (multibondIsingPartition ends J) -
        Real.log (multibondIsingPartition ends J')| ≤
      ∑ p : P, |J p - J' p| := by
  rw [multibondIsingPartition_eq_Z_neg_one,
    multibondIsingPartition_eq_Z_neg_one]
  simpa using StatMech.Ising.logZ_dist_le (-1)
    (multibondIsingAction ends J) (multibondIsingAction ends J')
    (∑ p : P, |J p - J' p|)
    (multibondIsingAction_coupling_sub_abs_le ends J J')


theorem abs_multibondTwistCoupling_sub
    (J J' : P → Real) (D : Finset P) (p : P) :
    |multibondTwistCoupling J D p - multibondTwistCoupling J' D p| =
      |J p - J' p| := by
  by_cases hp : p ∈ D
  · rw [multibondTwistCoupling_apply_mem J D hp,
      multibondTwistCoupling_apply_mem J' D hp]
    have hneg : -J p - -J' p = -(J p - J' p) := by ring
    rw [hneg, abs_neg]
  · simp [multibondTwistCoupling, hp]


theorem multibondDisorderFreeEnergy_coupling_sub_abs_le
    (ends : P → V × V) (J J' : P → Real) (D : Finset P) :
    |multibondDisorderFreeEnergy ends J D -
        multibondDisorderFreeEnergy ends J' D| ≤
      2 * ∑ p : P, |J p - J' p| := by
  let A := Real.log (multibondIsingPartition ends J)
  let B := Real.log
    (multibondIsingPartition ends (multibondTwistCoupling J D))
  let A' := Real.log (multibondIsingPartition ends J')
  let B' := Real.log
    (multibondIsingPartition ends (multibondTwistCoupling J' D))
  have hordinary : |A - A'| ≤ ∑ p : P, |J p - J' p| :=
    multibondIsing_logPartition_coupling_sub_abs_le ends J J'
  have htwisted : |B - B'| ≤ ∑ p : P, |J p - J' p| := by
    have h := multibondIsing_logPartition_coupling_sub_abs_le ends
      (multibondTwistCoupling J D) (multibondTwistCoupling J' D)
    simpa only [abs_multibondTwistCoupling_sub] using h
  unfold multibondDisorderFreeEnergy
  change |(A - B) - (A' - B')| ≤ _
  calc
    |(A - B) - (A' - B')| = |(A - A') - (B - B')| := by ring_nf
    _ ≤ |A - A'| + |B - B'| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (A - A') (-(B - B'))
    _ ≤ (∑ p : P, |J p - J' p|) + ∑ p : P, |J p - J' p| :=
      add_le_add hordinary htwisted
    _ = 2 * ∑ p : P, |J p - J' p| := by ring


end
end StatMech.FrontierA
