/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingPositiveBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingBoundarySum
import Def.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingPositiveBoundary
open Equiv Finset


namespace StatMech.FrontierD

noncomputable section

theorem two_mul_sum_toNat_eq_sum_natAbs_of_sum_eq_zero
    {α : Type*} [Fintype α] (w : α -> Int)
    (hsum : ∑ a, w a = 0) :
    2 * (∑ a, (w a).toNat) = ∑ a, (w a).natAbs := by
  have hdiff :
      (∑ a, ((w a).toNat : Int)) -
          (∑ a, ((-w a).toNat : Int)) = 0 := by
    rw [← Finset.sum_sub_distrib]
    simpa only [Int.toNat_sub_toNat_neg] using hsum
  have hbalance : (∑ a, (w a).toNat) = ∑ a, (-w a).toNat := by
    exact_mod_cast sub_eq_zero.mp hdiff
  calc
    2 * (∑ a, (w a).toNat) =
        (∑ a, (w a).toNat) + ∑ a, (-w a).toNat := by omega
    _ = ∑ a, ((w a).toNat + (-w a).toNat) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ a, (w a).natAbs := by
      apply Finset.sum_congr rfl
      intro a _
      exact Int.toNat_add_toNat_neg_eq_natAbs (w a)


theorem fkRectUnorientedVerticalWindingTotal_eq_two_mul_positiveBoundary
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectUnorientedVerticalWindingTotal R omega =
      2 * fkRectPositiveVerticalBoundaryWindingTotal R omega := by
  rw [fkRectUnorientedVerticalWindingTotal,
    fkRectUnorientedVerticalWindingTotal_eq_sum_blackBoundaryCycle]
  symm
  exact two_mul_sum_toNat_eq_sum_natAbs_of_sum_eq_zero
    (fun C : FKRectConfigurationBlackBoundaryCycle R omega =>
      (fkRectBlackBoundaryCycleWinding R omega C).2)
    (sum_fkRectBlackBoundaryCycleWinding_snd_eq_zero R omega)


theorem fkRectUnorientedVerticalWindingNumber_eq_positiveBoundary
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectUnorientedVerticalWindingNumber R omega =
      fkRectPositiveVerticalBoundaryWindingTotal R omega := by
  unfold fkRectUnorientedVerticalWindingNumber
  rw [fkRectUnorientedVerticalWindingTotal_eq_two_mul_positiveBoundary]
  simp

end
end StatMech.FrontierD
