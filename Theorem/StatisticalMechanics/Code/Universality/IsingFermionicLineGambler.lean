/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLineGambler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part17
import Def.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part2


namespace StatMech.Universality

open Finset

noncomputable section

theorem isingLineStoppedKernel_nonneg (n t : Nat)
    (p q : IsingLineBox n) :
    0 ≤ isingLineStoppedKernel n t p q := by
  induction t generalizing p with
  | zero =>
      unfold isingLineStoppedKernel
      split_ifs <;> norm_num
  | succ t ih =>
      simp only [isingLineStoppedKernel]
      split_ifs with hp
      · exact ih p
      · have hw := ih (isingLineWest n p)
        have he := ih (isingLineEast n p hp)
        positivity

theorem isingLineStoppedKernel_sum_eq_one (n t : Nat)
    (p : IsingLineBox n) :
    ∑ q, isingLineStoppedKernel n t p q = 1 := by
  induction t generalizing p with
  | zero => simp [isingLineStoppedKernel]
  | succ t ih =>
      simp only [isingLineStoppedKernel]
      split_ifs with hp
      · exact ih p
      · rw [← Finset.sum_div, Finset.sum_add_distrib, ih, ih]
        norm_num

end
end StatMech.Universality
