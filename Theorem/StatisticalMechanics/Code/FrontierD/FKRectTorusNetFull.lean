/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusConnected.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectCyclicPred_iterate_zero_val {N : Nat} (hN : 0 < N)
    (n : Nat) (hn : n <= N) :
    ((SixVertexArrows.cyclicPred hN)^[n] (⟨0, hN⟩ : Fin N)).val =
      if n = 0 then 0 else N - n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hn' : n <= N := by omega
      simp only [SixVertexArrows.cyclicPred]
      rw [ih hn']
      by_cases hzero : n = 0
      · subst n
        simp only [ite_true, Nat.reduceAdd]
        rw [Nat.mod_eq_of_lt (by omega)]
        simp
      · simp only [hzero, ite_false]
        have hnlt : n < N := by omega
        have heq : N - n + N - 1 = (N - (n + 1)) + N := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        simp

theorem fkRectCyclicPred_val {N : Nat} (hN : 0 < N) (i : Fin N) :
    (SixVertexArrows.cyclicPred hN i).val =
      if i.val = 0 then N - 1 else i.val - 1 := by
  unfold SixVertexArrows.cyclicPred
  by_cases hi : i.val = 0
  · simp only [hi, ite_true, Nat.zero_add]
    rw [Nat.mod_eq_of_lt (by omega)]
  · simp only [hi, ite_false]
    have heq : i.val + N - 1 = (i.val - 1) + N := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

end
end StatMech.FrontierD
