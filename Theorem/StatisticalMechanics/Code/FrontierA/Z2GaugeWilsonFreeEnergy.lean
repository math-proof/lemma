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
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonFreeEnergy
open scoped BigOperators symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


@[simp] theorem multibondTwistCoupling_apply_mem
    (J : P → Real) (D : Finset P) {p : P} (hp : p ∈ D) :
    multibondTwistCoupling J D p = -J p := by
  simp [multibondTwistCoupling, hp]

@[simp] theorem multibondTwistCoupling_apply_not_mem
    (J : P → Real) (D : Finset P) {p : P} (hp : p ∉ D) :
    multibondTwistCoupling J D p = J p := by
  simp [multibondTwistCoupling, hp]


theorem multibond_twist_energy_eq_shiftedCut
    (ends : P → V × V) (J : P → Real) (D : Finset P) (s : V → Bool) :
    (∑ p : P, multibondTwistCoupling J D p) -
        2 * ∑ p ∈ multibondCut ends s, multibondTwistCoupling J D p =
      (∑ p : P, J p) - 2 * ∑ p ∈ multibondCut ends s ∆ D, J p := by
  classical
  have sum_indicator (S : Finset P) (f : P → Real) :
      (∑ p ∈ S, f p) = ∑ p : P, if p ∈ S then f p else 0 := by
    rw [← Finset.sum_filter]
    simp
  rw [sum_indicator (multibondCut ends s),
    sum_indicator (multibondCut ends s ∆ D),
    Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hcut : p ∈ multibondCut ends s <;>
    by_cases hD : p ∈ D <;>
    simp [multibondTwistCoupling, hcut, hD, mem_symmDiff] <;> ring


theorem multibondIsingWeight_twist_eq_shiftedActivity
    (ends : P → V × V) (J : P → Real) (D : Finset P) (s : V → Bool) :
    multibondIsingWeight ends (multibondTwistCoupling J D) s =
      Real.exp (∑ p : P, J p) *
        ∏ p ∈ multibondCut ends s ∆ D, Real.exp (-2 * J p) := by
  rw [multibondIsingWeight, multibond_energy_eq_sub_cut,
    multibond_twist_energy_eq_shiftedCut]
  rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_sum]
  congr 1
  congr 1
  rw [Finset.mul_sum]
  symm
  calc
    (∑ p ∈ multibondCut ends s ∆ D, -2 * J p) =
        ∑ p ∈ multibondCut ends s ∆ D, -(2 * J p) := by
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = -(∑ p ∈ multibondCut ends s ∆ D, 2 * J p) := by
      rw [Finset.sum_neg_distrib]


theorem multibondIsingPartition_twist_eq_shiftedActivity
    (root : V) (ends : P → V × V) (J : P → Real) (D : Finset P) :
    multibondIsingPartition ends (multibondTwistCoupling J D) =
      (2 * Real.exp (∑ p : P, J p)) *
        ∑ s : AnchoredConfig V root,
          ∏ p ∈ multibondCut ends s.1 ∆ D, Real.exp (-2 * J p) := by
  rw [multibondIsingPartition]
  calc
    (∑ s : V → Bool,
        multibondIsingWeight ends (multibondTwistCoupling J D) s) =
        ∑ bs : Bool × AnchoredConfig V root,
          multibondIsingWeight ends (multibondTwistCoupling J D)
            (unanchorConfig bs.1 bs.2) := by
      apply Fintype.sum_equiv (configEquivBoolAnchored root)
      intro s
      rw [show unanchorConfig ((configEquivBoolAnchored root s).1)
          ((configEquivBoolAnchored root s).2) = s from
        (configEquivBoolAnchored root).left_inv s]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [multibondIsingWeight_twist_eq_shiftedActivity,
        multibondCut_unanchorConfig]
      rw [Fintype.sum_bool]
      rw [← Finset.mul_sum]
      ring


theorem multibondIsingPartition_pos
    (ends : P → V × V) (J : P → Real) :
    0 < multibondIsingPartition ends J := by
  unfold multibondIsingPartition multibondIsingWeight
  positivity


end
end StatMech.FrontierA
