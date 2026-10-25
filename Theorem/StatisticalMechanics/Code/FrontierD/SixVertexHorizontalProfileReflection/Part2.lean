/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileSign
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexCyclicNeg_even_iff
    {N : Nat} (hN : 0 < N) (hEven : Even N) (i : Fin N) :
    Even (sixVertexCyclicNeg hN i).val ↔ Even i.val := by
  by_cases hi : i.val = 0
  · have hieq : i = ⟨0, hN⟩ := Fin.ext hi
    subst i
    simp
  · rw [sixVertexCyclicNeg_val_of_ne_zero hN i hi,
      Nat.even_sub (Nat.le_of_lt i.isLt)]
    simp [hEven]

theorem sixVertexCyclicNeg_cyclicPred
    {N : Nat} (hN : 0 < N) (i : Fin N) :
    sixVertexCyclicNeg hN (SixVertexArrows.cyclicPred hN i) =
      finitePeriodicSucc hN (sixVertexCyclicNeg hN i) := by
  apply Fin.ext
  by_cases hN1 : N = 1
  · subst N
    simp [sixVertexCyclicNeg, SixVertexArrows.cyclicPred,
      finitePeriodicSucc]
  · have hNtwo : 2 ≤ N := by omega
    by_cases hi0 : i.val = 0
    · have hpredVal :
          (SixVertexArrows.cyclicPred hN i).val = N - 1 := by
        change (i.val + N - 1) % N = N - 1
        rw [hi0]
        simp
      have hpredNe :
          (SixVertexArrows.cyclicPred hN i).val ≠ 0 := by
        rw [hpredVal]
        omega
      rw [sixVertexCyclicNeg_val_of_ne_zero hN _ hpredNe,
        hpredVal]
      unfold finitePeriodicSucc
      simp only
      have hnegZero : (sixVertexCyclicNeg hN i).val = 0 := by
        have hieq : i = ⟨0, hN⟩ := Fin.ext hi0
        subst i
        simp
      rw [hnegZero, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
      omega
    · have hiPos : 0 < i.val := Nat.pos_of_ne_zero hi0
      have hpredVal :
          (SixVertexArrows.cyclicPred hN i).val = i.val - 1 := by
        unfold SixVertexArrows.cyclicPred
        simp only
        rw [show i.val + N - 1 = N + (i.val - 1) by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      by_cases hi1 : i.val = 1
      · have hpredZero :
            SixVertexArrows.cyclicPred hN i = ⟨0, hN⟩ := by
          apply Fin.ext
          rw [hpredVal, hi1]
        rw [hpredZero, sixVertexCyclicNeg_zero]
        unfold finitePeriodicSucc
        change 0 = ((sixVertexCyclicNeg hN i).val + 1) % N
        rw [sixVertexCyclicNeg_val_of_ne_zero hN i hi0, hi1]
        rw [show N - 1 + 1 = N by omega, Nat.mod_self]
      · have hpredNe :
            (SixVertexArrows.cyclicPred hN i).val ≠ 0 := by
          rw [hpredVal]
          omega
        rw [sixVertexCyclicNeg_val_of_ne_zero hN _ hpredNe,
          hpredVal]
        unfold finitePeriodicSucc
        change N - (i.val - 1) =
          ((sixVertexCyclicNeg hN i).val + 1) % N
        rw [sixVertexCyclicNeg_val_of_ne_zero hN i hi0]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega

end
end StatMech.FrontierD
