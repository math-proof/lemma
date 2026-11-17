import Lemma.List.EqLengthGetSlicedIndices'.of.LeSubAddMul.GtSubAddMul
open List


private lemma sliced_indices'_congr_start
  {stop N step start start' : ℕ}
  (h_eq : start = start')
  (h_gt : start > stop)
  (h_le : start ≤ N)
  (h_step : step > 0) :
  Nat.sliced_indices' h_gt h_le h_step =
    Nat.sliced_indices' (start := start') (h_eq ▸ h_gt) (h_eq ▸ h_le) h_step := by
  cases h_eq
  rfl


@[path]
private lemma main
  {j' : Fin d}
-- given
  (h_stop : n * d + j > j + j')
  (h_start : n * d + j ≤ N)
  (h_i : i < n) :
-- imply
  (Nat.sliced_indices' h_stop h_start (Nat.Gt_0 j'))[i]'(by
    rw [EqLengthGetSlicedIndices'.of.LeSubAddMul.GtSubAddMul h_stop h_start]
    exact h_i) = (n - i) * d + j - 1 := by
-- proof
  induction n generalizing i j with
  | zero =>
    simp
    linarith
  | succ n ih =>
    have h_start_eq : (n + 1) * d + j - d = n * d + j := by
      rw [Nat.succ_mul, Nat.add_right_comm]
      exact Nat.add_sub_cancel (n * d + j) d
    unfold Nat.sliced_indices'
    split_ifs with h_rec
    ·
      match i with
      | 0 =>
        simp
      | i + 1 =>
        simp
        have h_stop' : n * d + j > j + ↑j' := by
          simpa [h_start_eq] using h_rec
        have h_start' : n * d + j ≤ N := by
          calc
            n * d + j ≤ n * d + j + d := Nat.le_add_right _ _
            _ = (n + 1) * d + j := by rw [Nat.add_right_comm, Nat.succ_mul]
            _ ≤ N := h_start
        have hih := ih (i := i) (j := j) h_stop' h_start' (Nat.lt_of_succ_lt_succ h_i)
        have hmain : ∀ (hle' : (n + 1) * d + j - d ≤ N)
            (hidx : i < (Nat.sliced_indices' h_rec hle' (Nat.Gt_0 j')).length),
            ((Nat.sliced_indices' h_rec hle' (Nat.Gt_0 j')).get ⟨i, hidx⟩ : ℕ) =
              (n - i) * d + j - 1 := by
          intro hle' hidx
          have hlists :
              Nat.sliced_indices' h_rec hle' (Nat.Gt_0 j') =
                Nat.sliced_indices' h_stop' h_start' (Nat.Gt_0 j') := by
            rw [sliced_indices'_congr_start (start := (n + 1) * d + j - d)
              (start' := n * d + j) h_start_eq]
          have hidx' : i < (Nat.sliced_indices' h_stop' h_start' (Nat.Gt_0 j')).length := by
            rw [← hlists]; exact hidx
          have : ((Nat.sliced_indices' h_rec hle' (Nat.Gt_0 j')).get ⟨i, hidx⟩ : ℕ) =
              ((Nat.sliced_indices' h_stop' h_start' (Nat.Gt_0 j')).get ⟨i, hidx'⟩ : ℕ) := by
            simp [hlists]
          rw [this, List.get_eq_getElem]
          exact hih
        exact hmain _ _
    ·
      have hn0 : n = 0 := by
        have hj' : (j' : ℕ) < d := j'.isLt
        have hle : (n + 1) * d + j - d ≤ j + (j' : ℕ) := Nat.not_lt.mp h_rec
        have hle' : n * d ≤ (j' : ℕ) := by
          rw [h_start_eq] at hle
          omega
        have hlt : n * d < d := Nat.lt_of_le_of_lt hle' hj'
        cases n with
        | zero => rfl
        | succ n =>
          have : d ≤ (n + 1) * d := Nat.le_mul_of_pos_left d (Nat.succ_pos _)
          exact (Nat.not_le_of_gt hlt).elim this
      subst hn0
      have hi0 : i = 0 := Nat.lt_one_iff.mp h_i
      subst hi0
      simp


-- created on 2025-11-09
