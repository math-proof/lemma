/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk.Part6
import Def.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part3


namespace StatMech.Universality

open Finset

noncomputable section

theorem isingLeapfrogExitKernelTimeGradientSq_eq_sum_boundary
    (R t t' : Nat) (p p' : IsingLeapfrogBox R) :
    isingLeapfrogExitKernelTimeGradientSq R t t' p p' =
      ∑ q with isingLeapfrogBoxBoundary R q,
        (isingLeapfrogStoppedKernel R t p q -
          isingLeapfrogStoppedKernel R t' p' q) ^ 2 := by
  classical
  unfold isingLeapfrogExitKernelTimeGradientSq isingLeapfrogExitKernel
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hb : isingLeapfrogBoxBoundary R q <;> simp [hb]

theorem isingLeapfrogStoppedKernelTimeGradientSq_le_killed_add_exit
    (R t t' : Nat) (p p' : IsingLeapfrogBox R) :
    isingLeapfrogStoppedKernelTimeGradientSq R t t' p p' ≤
      2 * (isingLeapfrogKilledKernelTimeGradientSq R t t' p p' +
        isingLeapfrogExitKernelTimeGradientSq R t t' p p') := by
  classical
  unfold isingLeapfrogStoppedKernelTimeGradientSq
    isingLeapfrogKilledKernelTimeGradientSq
    isingLeapfrogExitKernelTimeGradientSq
  calc
    _ ≤ ∑ q, 2 *
        ((isingLeapfrogKilledKernel R t p q -
            isingLeapfrogKilledKernel R t' p' q) ^ 2 +
          (isingLeapfrogExitKernel R t p q -
            isingLeapfrogExitKernel R t' p' q) ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      rw [isingLeapfrogStoppedKernel_eq_killed_add_exit R t p q,
        isingLeapfrogStoppedKernel_eq_killed_add_exit R t' p' q]
      nlinarith [sq_nonneg
        ((isingLeapfrogKilledKernel R t p q -
            isingLeapfrogKilledKernel R t' p' q) -
          (isingLeapfrogExitKernel R t p q -
            isingLeapfrogExitKernel R t' p' q))]
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]


end
end StatMech.Universality
