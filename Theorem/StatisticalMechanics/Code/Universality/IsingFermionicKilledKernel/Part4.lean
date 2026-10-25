/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk.Part6
import Def.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part4


namespace StatMech.Universality

open Finset

noncomputable section

theorem isingLeapfrogFreeKernel_nonneg (t : Nat)
    (p q : IsingLeapfrogPlane) :
    0 ≤ isingLeapfrogFreeKernel t p q := by
  induction t generalizing p with
  | zero =>
      unfold isingLeapfrogFreeKernel
      split_ifs <;> norm_num
  | succ t ih =>
      simp only [isingLeapfrogFreeKernel]
      have hSW := ih (isingLeapfrogPlaneSW p)
      have hSE := ih (isingLeapfrogPlaneSE p)
      have hNW := ih (isingLeapfrogPlaneNW p)
      have hNE := ih (isingLeapfrogPlaneNE p)
      positivity

theorem isingBinomialWeight_succ (t k : Nat) :
    isingBinomialWeight (t + 1) k =
      (isingBinomialWeight t k + isingBinomialWeightPrev t k) / 2 := by
  cases k with
  | zero =>
      simp [isingBinomialWeight, isingBinomialWeightPrev, pow_succ]
      ring
  | succ k =>
      unfold isingBinomialWeight isingBinomialWeightPrev
      simp only [Nat.succ_ne_zero, if_false, Nat.succ_sub_one]
      rw [Nat.choose_succ_succ']
      push_cast
      simp only [isingBinomialWeight]
      rw [pow_succ]
      ring


end
end StatMech.Universality
