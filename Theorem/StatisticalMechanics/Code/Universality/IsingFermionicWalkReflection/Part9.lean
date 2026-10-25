/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part10


namespace StatMech.Universality

theorem isingLeapfrogStoppedKernel_one_eq_pathCount_div (R : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogStoppedKernel R 1 p q =
      isingLeapfrogStoppedOneStepCount R p q / 4 := by
  by_cases hp : isingLeapfrogBoxBoundary R p
  · simp only [isingLeapfrogStoppedKernel, dif_pos hp]
    unfold isingLeapfrogStoppedOneStepCount
    rw [dif_pos hp]
    by_cases hpq : p = q <;> simp [hpq]
  · simp only [isingLeapfrogStoppedKernel, dif_neg hp]
    unfold isingLeapfrogStoppedOneStepCount
    rw [dif_neg hp]
    push_cast
    congr


theorem isingLeapfrogKilled_mul_stopped_one_eq_pathCount_div
    (R t : Nat) (p r q : IsingLeapfrogBox R) :
    isingLeapfrogKilledKernel R t p r *
        isingLeapfrogStoppedKernel R 1 r q =
      (isingLeapfrogKilledPathCount R t p r *
          isingLeapfrogStoppedOneStepCount R r q : Nat) /
        (4 : Real) ^ (t + 1) := by
  rw [isingLeapfrogKilledKernel_eq_pathCount_div,
    isingLeapfrogStoppedKernel_one_eq_pathCount_div]
  push_cast
  rw [pow_succ]
  ring


end StatMech.Universality
