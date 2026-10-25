/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk.Part6
import Def.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel


namespace StatMech.Universality

open Finset

noncomputable section

theorem isingLeapfrogStoppedKernel_eq_killed_add_exit (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogStoppedKernel R t p q =
      isingLeapfrogKilledKernel R t p q +
        isingLeapfrogExitKernel R t p q := by
  by_cases hq : isingLeapfrogBoxBoundary R q <;>
    simp [isingLeapfrogKilledKernel, isingLeapfrogExitKernel, hq]

theorem isingLeapfrogKilledKernel_nonneg (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    0 ≤ isingLeapfrogKilledKernel R t p q := by
  unfold isingLeapfrogKilledKernel
  split_ifs
  · exact le_rfl
  · exact isingLeapfrogStoppedKernel_nonneg R t p q

theorem isingLeapfrogExitKernel_nonneg (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    0 ≤ isingLeapfrogExitKernel R t p q := by
  unfold isingLeapfrogExitKernel
  split_ifs
  · exact isingLeapfrogStoppedKernel_nonneg R t p q
  · exact le_rfl

theorem isingLeapfrogExitKernel_le_one (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogExitKernel R t p q ≤ 1 := by
  unfold isingLeapfrogExitKernel
  split_ifs
  · exact isingLeapfrogStoppedKernel_le_one R t p q
  · norm_num

theorem isingLeapfrogExitKernel_mono (R : Nat)
    (p q : IsingLeapfrogBox R) :
    Monotone (fun t ↦ isingLeapfrogExitKernel R t p q) := by
  apply monotone_nat_of_le_succ
  intro t
  by_cases hq : isingLeapfrogBoxBoundary R q
  · unfold isingLeapfrogExitKernel
    simp only [if_pos hq]
    exact isingLeapfrogStoppedKernel_boundary_mono R t p q hq
  · simp [isingLeapfrogExitKernel, hq]


end
end StatMech.Universality
