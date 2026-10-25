/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part11


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem lineBoundaryString_leftInverse (m K : Nat) (hm : 0 < m) :
    Function.LeftInverse (lineBoundarySumToString m K)
      (lineBoundaryStringToSum m K hm) := by
  intro w
  unfold lineBoundaryStringToSum
  by_cases hzero : (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ w.1).1 = 0
  · rw [dif_pos hzero]
    rfl
  · rw [dif_neg hzero]
    rfl

theorem lineBoundaryString_rightInverse (m K : Nat) (hm : 0 < m) :
    Function.RightInverse (lineBoundarySumToString m K)
      (lineBoundaryStringToSum m K hm) := by
  intro w
  cases w with
  | inl w =>
      unfold lineBoundarySumToString lineBoundaryStringToSum
      have hzero : (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ w.1).1 = 0 := by
        simp [w.2.2]
      rw [dif_pos hzero]
      apply congrArg Sum.inl
      apply Subtype.ext
      rfl
  | inr w =>
      unfold lineBoundarySumToString lineBoundaryStringToSum
      have hne : (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ w.1).1 ≠ 0 := by
        simp [w.2.2]
        omega
      rw [dif_neg hne]
      apply congrArg Sum.inr
      apply Subtype.ext
      rfl

end
end StatMech.Universality
