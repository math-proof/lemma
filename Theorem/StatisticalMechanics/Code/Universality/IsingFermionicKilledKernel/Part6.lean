/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk.Part6
import Def.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part6


namespace StatMech.Universality

open Finset

noncomputable section

theorem isingLeapfrogFreeKernel_eq_binomial (t : Nat)
    (p q : IsingLeapfrogPlane) :
    isingLeapfrogFreeKernel t p q =
      isingLeapfrogFreeBinomialKernel t p q := by
  induction t generalizing p with
  | zero =>
      unfold isingLeapfrogFreeKernel isingLeapfrogFreeBinomialKernel
        isingLineBinomialKernel isingBinomialWeight
      simp only [Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add, Nat.choose_zero_right, Nat.cast_one,
        pow_zero, div_one]
      split_ifs <;> simp_all [Prod.ext_iff]
  | succ t ih =>
      simp only [isingLeapfrogFreeKernel]
      rw [ih, ih, ih, ih]
      unfold isingLeapfrogFreeBinomialKernel isingLeapfrogPlaneSW
        isingLeapfrogPlaneSE isingLeapfrogPlaneNW isingLeapfrogPlaneNE
      rw [isingLineBinomialKernel_succ,
        isingLineBinomialKernel_succ]
      ring

end
end StatMech.Universality
