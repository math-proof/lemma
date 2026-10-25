/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedOrbitInteraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryOrbitVisits.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectRefinedOrbitInteraction
open scoped BigOperators
open Equiv Finset


namespace StatMech.FrontierD

noncomputable section

theorem permOrbitSignedVisitTrace_eq_sum_range
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (sigma : Perm alpha) (d a b : alpha) (n : Nat) :
    permOrbitSignedVisitTrace sigma d a b n =
      Finset.sum (range n) fun i =>
        ((if (sigma ^ i) d = a then 1 else 0) : Int) -
          (if (sigma ^ i) d = b then 1 else 0) := by
  induction n generalizing d with
  | zero => simp [permOrbitSignedVisitTrace]
  | succ n ih =>
      rw [permOrbitSignedVisitTrace, ih, sum_range_succ']
      have htail :
          (∑ i ∈ range n,
            (((if (sigma ^ i) (sigma d) = a then 1 else 0) : Int) -
              (if (sigma ^ i) (sigma d) = b then 1 else 0))) =
            ∑ i ∈ range n,
              (((if (sigma ^ (i + 1)) d = a then 1 else 0) : Int) -
                (if (sigma ^ (i + 1)) d = b then 1 else 0)) := by
        apply sum_congr rfl
        intro i hi
        simp only [pow_succ, Perm.mul_apply]
      rw [htail]
      simp only [Nat.one_add, pow_zero, Perm.one_apply]
      abel


theorem permOrbitSignedVisitTrace_orderOf
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (sigma : Perm alpha) (d a b : alpha) :
    permOrbitSignedVisitTrace sigma d a b (orderOf sigma) =
      (permOrbitVisitCount sigma d a : Int) -
        permOrbitVisitCount sigma d b := by
  rw [permOrbitSignedVisitTrace_eq_sum_range]
  rw [← Fin.sum_univ_eq_sum_range]
  unfold permOrbitVisitCount
  push_cast
  rw [Finset.sum_sub_distrib]


end
end StatMech.FrontierD
