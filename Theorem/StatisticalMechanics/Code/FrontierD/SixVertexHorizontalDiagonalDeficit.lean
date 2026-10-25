/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalDiagonalDeficit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalResidualCompletions.Part3


namespace StatMech.FrontierD

noncomputable section

theorem natChoose_logConcave_of_pos (n k : Nat) (hk : 0 < k) :
    Nat.choose n (k - 1) * Nat.choose n (k + 1) <=
      Nat.choose n k * Nat.choose n k := by
  by_cases hkn : k <= n
  · have hprev : Nat.choose n (k - 1) * (n - (k - 1)) =
        Nat.choose n k * k := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      simpa using (Nat.choose_succ_right_eq n j).symm
    have hnext : Nat.choose n (k + 1) * (k + 1) =
        Nat.choose n k * (n - k) :=
      Nat.choose_succ_right_eq n k
    have hsub : n - (k - 1) = n - k + 1 := by omega
    have hfactor : k * (n - k) <= (n - (k - 1)) * (k + 1) := by
      rw [hsub]
      nlinarith
    have hbig : 0 < (n - (k - 1)) * (k + 1) := by
      rw [hsub]
      positivity
    have heq :
        (Nat.choose n (k - 1) * Nat.choose n (k + 1)) *
            ((n - (k - 1)) * (k + 1)) =
          (Nat.choose n k * Nat.choose n k) * (k * (n - k)) := by
      calc
        _ = (Nat.choose n (k - 1) * (n - (k - 1))) *
              (Nat.choose n (k + 1) * (k + 1)) := by ring
        _ = (Nat.choose n k * k) * (Nat.choose n k * (n - k)) := by
          rw [hprev, hnext]
        _ = _ := by ring
    have hmul :
        (Nat.choose n (k - 1) * Nat.choose n (k + 1)) *
            ((n - (k - 1)) * (k + 1)) <=
          (Nat.choose n k * Nat.choose n k) *
            ((n - (k - 1)) * (k + 1)) := by
      rw [heq]
      exact Nat.mul_le_mul_left _ hfactor
    exact Nat.le_of_mul_le_mul_right hmul hbig
  · have hnk : n < k := Nat.lt_of_not_ge hkn
    rw [Nat.choose_eq_zero_of_lt hnk,
      Nat.choose_eq_zero_of_lt (hnk.trans_le (Nat.le_add_right k 1))]
    simp

end
end StatMech.FrontierD
