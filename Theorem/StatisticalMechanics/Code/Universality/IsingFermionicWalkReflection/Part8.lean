/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part9


namespace StatMech.Universality

theorem isingLeapfrogKilledKernel_eq_pathCount_div (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogKilledKernel R t p q =
      isingLeapfrogKilledPathCount R t p q / (4 : Real) ^ t := by
  induction t generalizing p with
  | zero =>
      simp [isingLeapfrogKilledKernel, isingLeapfrogKilledPathCount,
        isingLeapfrogStoppedKernel]
  | succ t ih =>
      by_cases hq : isingLeapfrogBoxBoundary R q
      · simp [isingLeapfrogKilledKernel, isingLeapfrogKilledPathCount, hq]
      · by_cases hp : isingLeapfrogBoxBoundary R p
        · have ihp := ih p
          simp only [isingLeapfrogKilledKernel, if_neg hq] at ihp
          simp only [isingLeapfrogKilledKernel, if_neg hq,
            isingLeapfrogStoppedKernel, dif_pos hp,
            isingLeapfrogKilledPathCount]
          rw [ihp]
          push_cast
          rw [pow_succ]
          ring
        · simp only [isingLeapfrogKilledKernel, if_neg hq,
            isingLeapfrogStoppedKernel, dif_neg hp,
            isingLeapfrogKilledPathCount]
          have hSW := ih (isingLeapfrogSW R p)
          have hSE := ih (isingLeapfrogSE R p hp)
          have hNW := ih (isingLeapfrogNW R p hp)
          have hNE := ih (isingLeapfrogNE R p hp)
          simp only [isingLeapfrogKilledKernel, if_neg hq] at hSW hSE hNW hNE
          rw [hSW, hSE, hNW, hNE]
          push_cast
          rw [pow_succ]
          ring


end StatMech.Universality
