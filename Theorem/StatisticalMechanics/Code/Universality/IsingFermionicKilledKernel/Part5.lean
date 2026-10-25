/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk.Part6
import Def.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part5


namespace StatMech.Universality

open Finset

noncomputable section

theorem isingLineBinomialKernel_succ (t : Nat) (x y : Int) :
    isingLineBinomialKernel (t + 1) x y =
      (isingLineBinomialKernel t (x - 1) y +
        isingLineBinomialKernel t (x + 1) y) / 2 := by
  unfold isingLineBinomialKernel
  rw [show t + 1 + 1 = t + 2 by omega]
  simp_rw [isingBinomialWeight_succ]
  have hsplit (k : Nat) :
      (if y = x + 2 * (k : Int) - (t + 1 : Nat) then
          (isingBinomialWeight t k + isingBinomialWeightPrev t k) / 2
        else 0) =
        ((if y = x + 2 * (k : Int) - (t + 1 : Nat) then
            isingBinomialWeight t k else 0) +
          (if y = x + 2 * (k : Int) - (t + 1 : Nat) then
            isingBinomialWeightPrev t k else 0)) / 2 := by
    split_ifs <;> simp
  simp_rw [hsplit]
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [show t + 2 = (t + 1) + 1 by omega,
      Finset.sum_range_succ]
    simp only [isingBinomialWeight, Nat.choose_succ_self, Nat.cast_zero,
      zero_div, ite_self, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    have heq :
        (y = x + 2 * (k : Int) - (t + 1 : Nat)) ↔
          (y = x - 1 + 2 * (k : Int) - (t : Int)) := by omega
    simp only [heq]
  · rw [show t + 2 = (t + 1) + 1 by omega,
      Finset.sum_range_succ']
    simp only [isingBinomialWeightPrev, Nat.add_one_ne_zero, if_false,
      Nat.add_sub_cancel, if_true, ite_self, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    have heq :
        (y = x + 2 * ((k + 1 : Nat) : Int) - (t + 1 : Nat)) ↔
          (y = x + 1 + 2 * (k : Int) - (t : Int)) := by
      push_cast
      omega
    simp only [heq]

end
end StatMech.Universality
