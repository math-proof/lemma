import Lemma.Fin.Sum_MulDeltaS.eq.Delta
import Lemma.Nat.Delta
import Lemma.Tensor.EqMul0_0
import Lemma.Tensor.EqMul_0'0
import Lemma.Tensor.EqMul_1
import Lemma.Tensor.GetDot.eq.Sum_MulGetS
import Lemma.Tensor.GetEye.eq.Delta
import Lemma.Tensor.GetShiftMatrix.eq.Ite
open Fin Nat Tensor
set_option maxHeartbeats 500000


private lemma eye_cell_eq
  [Semiring α] [CharZero α]
  (n i₀ j₀ : ℕ) (hi₀ : i₀ < n) (hj₀ : j₀ < n)
  (i j : Fin n)
  (h_eq : i₀ = j₀) :
  (((ShiftMatrix (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩) @
      ShiftMatrix (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩).get i).get j =
    ((eye (α := α) n).get i).get j := by
  have h := GetDot.eq.Sum_MulGetS
    (ShiftMatrix (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩)
    (ShiftMatrix (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩) i j
  have heye := GetEye.eq.Delta.fin (α := α) i j
  conv_rhs => erw [heye]
  apply h.trans
  subst h_eq
  apply (Finset.sum_eq_single i _ _).trans _
  ·
    intro k _ hk
    have hqk := GetShiftMatrix.eq.Ite (α := α) ⟨i₀, hi₀⟩ ⟨i₀, hi₀⟩ i k
    have hpk := GetShiftMatrix.eq.Ite (α := α) ⟨i₀, hi₀⟩ ⟨i₀, hi₀⟩ k j
    simp only [GetElem.getElem] at hqk hpk ⊢
    simp only [hqk, hpk]
    simp only [id, Nat.Delta.eq.Ite, ← Fin.val_eq_val]
    have hkn : (k : ℕ) ≠ (i : ℕ) := fun h => hk (Fin.ext h)
    simp
    split_ifs
    aesop
    aesop
    repeat apply EqMul0_0.nat
  ·
    intro h
    exact (h (Finset.mem_univ _)).elim
  ·
    have hqk := GetShiftMatrix.eq.Ite (α := α) ⟨i₀, hi₀⟩ ⟨i₀, hi₀⟩ i i
    have hpk := GetShiftMatrix.eq.Ite (α := α) ⟨i₀, hi₀⟩ ⟨i₀, hi₀⟩ i j
    simp only [GetElem.getElem] at hqk hpk ⊢
    simp only [hqk, hpk]
    simp only [id, Nat.Delta.eq.Ite, ← Fin.val_eq_val]
    simp
    split_ifs
    · apply Tensor.EqMul_1.nat
    · exact (Tensor.EqMul_0'0.nat _).trans Nat.cast_zero.symm


private lemma eye_cell_lt_i0
  [Semiring α] [CharZero α]
  (n i₀ j₀ : ℕ) (hi₀ : i₀ < n) (hj₀ : j₀ < n)
  (i j : Fin n)
  (h_eq : ¬ i₀ = j₀)
  (h_lt : i₀ < j₀)
  (hi0 : (i : ℕ) = i₀) :
  (((ShiftMatrix (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩) @
      ShiftMatrix (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩).get i).get j =
    ((eye (α := α) n).get i).get j := by
  have h := GetDot.eq.Sum_MulGetS
    (ShiftMatrix (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩)
    (ShiftMatrix (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩) i j
  have heye := GetEye.eq.Delta.fin (α := α) i j
  conv_rhs => erw [heye]
  apply h.trans
  apply (Finset.sum_eq_single ⟨j₀, hj₀⟩ _ _).trans _
  ·
    intro k _ hk
    have hqk := GetShiftMatrix.eq.Ite (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩ i k
    have hpk := GetShiftMatrix.eq.Ite (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩ k j
    simp only [GetElem.getElem] at hqk hpk ⊢
    simp only [hqk, hpk]
    simp only [id, Nat.Delta.eq.Ite, ← Fin.val_eq_val]
    have hkn : (k : ℕ) ≠ j₀ := fun h => hk (Fin.ext (by simp; exact h))
    simp [ite_eq_right (show ¬ j₀ = i₀ by grind), ite_eq_right (show ¬j₀ < i₀ by grind), ite_eq_right (show ¬↑k = j₀ by grind), ite_eq_left h_lt, ite_eq_right (show ¬ i₀ = j₀ by grind)]
    split_ifs
    omega
    apply Tensor.EqMul_0'0.nat
    apply Tensor.EqMul0_0.nat
    apply Tensor.EqMul0_0.nat
    omega
    omega
    apply Tensor.EqMul0_0.nat
    apply Tensor.EqMul0_0.nat
  ·
    intro h
    exact (h (Finset.mem_univ _)).elim
  ·
    have hqk := GetShiftMatrix.eq.Ite (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩ i ⟨j₀, hj₀⟩
    have hpk := GetShiftMatrix.eq.Ite (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩ ⟨j₀, hj₀⟩ j
    simp only [GetElem.getElem] at hqk hpk ⊢
    simp only [hqk, hpk]
    simp only [id, Nat.Delta.eq.Ite, ← Fin.val_eq_val]
    split_ifs <;> first
      | rfl
      | apply Tensor.EqMul_1.nat
      | apply Tensor.EqMul_0'0.nat
      | apply Tensor.EqMul0_0.nat
      | exact (Tensor.EqMul_0'0.nat _).trans Nat.cast_zero.symm
      | exact (Tensor.EqMul0_0.nat _).trans Nat.cast_zero.symm
      | exfalso; omega


private lemma eye_cell_lt_mid
  [Semiring α] [CharZero α]
  (n i₀ j₀ : ℕ) (hi₀ : i₀ < n) (hj₀ : j₀ < n)
  (i j : Fin n)
  (h_eq : ¬ i₀ = j₀)
  (h_lt : i₀ < j₀)
  (hi0 : (i : ℕ) ≠ i₀)
  (hi1 : i₀ < (i : ℕ) ∧ (i : ℕ) ≤ j₀) :
  (((ShiftMatrix (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩) @
      ShiftMatrix (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩).get i).get j =
    ((eye (α := α) n).get i).get j := by
  have h := GetDot.eq.Sum_MulGetS
    (ShiftMatrix (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩)
    (ShiftMatrix (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩) i j
  have heye := GetEye.eq.Delta.fin (α := α) i j
  conv_rhs => erw [heye]
  apply h.trans
  apply (Finset.sum_eq_single ⟨(i : ℕ) - 1, by omega⟩ _ _).trans _
  ·
    intro k _ hk
    have hqk := GetShiftMatrix.eq.Ite (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩ i k
    have hpk := GetShiftMatrix.eq.Ite (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩ k j
    simp only [GetElem.getElem] at hqk hpk ⊢
    simp only [hqk, hpk]
    simp only [id, Nat.Delta.eq.Ite, ← Fin.val_eq_val]
    have hkn : (k : ℕ) ≠ (i : ℕ) - 1 := fun h => hk (Fin.ext (by simp; exact h))
    split_ifs <;> first
      | rfl
      | apply Tensor.EqMul_1.nat
      | apply Tensor.EqMul_0'0.nat
      | apply Tensor.EqMul0_0.nat
      | exact (Tensor.EqMul_0'0.nat _).trans Nat.cast_zero.symm
      | exact (Tensor.EqMul0_0.nat _).trans Nat.cast_zero.symm
      | exfalso; omega
  ·
    intro h
    exact (h (Finset.mem_univ _)).elim
  ·
    have hqk := GetShiftMatrix.eq.Ite (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩ i ⟨(i : ℕ) - 1, by omega⟩
    have hpk := GetShiftMatrix.eq.Ite (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩ ⟨(i : ℕ) - 1, by omega⟩ j
    simp only [GetElem.getElem] at hqk hpk ⊢
    simp only [hqk, hpk]
    simp only [id, Nat.Delta.eq.Ite, ← Fin.val_eq_val]
    split_ifs <;> first
      | rfl
      | apply Tensor.EqMul_1.nat
      | apply Tensor.EqMul_0'0.nat
      | apply Tensor.EqMul0_0.nat
      | exact (Tensor.EqMul_0'0.nat _).trans Nat.cast_zero.symm
      | exact (Tensor.EqMul0_0.nat _).trans Nat.cast_zero.symm
      | exfalso; omega


private lemma eye_cell_lt_else
  [Semiring α] [CharZero α]
  (n i₀ j₀ : ℕ) (hi₀ : i₀ < n) (hj₀ : j₀ < n)
  (i j : Fin n)
  (h_eq : ¬ i₀ = j₀)
  (h_lt : i₀ < j₀)
  (hi0 : (i : ℕ) ≠ i₀)
  (hi1 : ¬ (i₀ < (i : ℕ) ∧ (i : ℕ) ≤ j₀)) :
  (((ShiftMatrix (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩) @
      ShiftMatrix (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩).get i).get j =
    ((eye (α := α) n).get i).get j := by
  have h := GetDot.eq.Sum_MulGetS
    (ShiftMatrix (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩)
    (ShiftMatrix (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩) i j
  have heye := GetEye.eq.Delta.fin (α := α) i j
  conv_rhs => erw [heye]
  apply h.trans
  apply (Finset.sum_eq_single i _ _).trans _
  ·
    intro k _ hk
    have hqk := GetShiftMatrix.eq.Ite (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩ i k
    have hpk := GetShiftMatrix.eq.Ite (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩ k j
    simp only [GetElem.getElem] at hqk hpk ⊢
    simp only [hqk, hpk]
    simp only [id, Nat.Delta.eq.Ite, ← Fin.val_eq_val]
    have hkn : (k : ℕ) ≠ (i : ℕ) := fun h => hk (Fin.ext h)
    split_ifs <;> first
      | rfl
      | apply Tensor.EqMul_1.nat
      | apply Tensor.EqMul_0'0.nat
      | apply Tensor.EqMul0_0.nat
      | exact (Tensor.EqMul_0'0.nat _).trans Nat.cast_zero.symm
      | exact (Tensor.EqMul0_0.nat _).trans Nat.cast_zero.symm
      | exfalso; omega
  ·
    intro h
    exact (h (Finset.mem_univ _)).elim
  ·
    have hqk := GetShiftMatrix.eq.Ite (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩ i i
    have hpk := GetShiftMatrix.eq.Ite (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩ i j
    simp only [GetElem.getElem] at hqk hpk ⊢
    simp only [hqk, hpk]
    simp only [id, Nat.Delta.eq.Ite, ← Fin.val_eq_val]
    split_ifs <;> first
      | rfl
      | apply Tensor.EqMul_1.nat
      | apply Tensor.EqMul_0'0.nat
      | apply Tensor.EqMul0_0.nat
      | exact (Tensor.EqMul_0'0.nat _).trans Nat.cast_zero.symm
      | exact (Tensor.EqMul0_0.nat _).trans Nat.cast_zero.symm
      | exfalso; omega


private lemma eye_cell_gt_i0
  [Semiring α] [CharZero α]
  (n i₀ j₀ : ℕ) (hi₀ : i₀ < n) (hj₀ : j₀ < n)
  (i j : Fin n)
  (h_eq : ¬ i₀ = j₀)
  (h_lt : ¬ i₀ < j₀)
  (hi0 : (i : ℕ) = i₀) :
  (((ShiftMatrix (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩) @
      ShiftMatrix (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩).get i).get j =
    ((eye (α := α) n).get i).get j := by
  have h := GetDot.eq.Sum_MulGetS
    (ShiftMatrix (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩)
    (ShiftMatrix (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩) i j
  have heye := GetEye.eq.Delta.fin (α := α) i j
  conv_rhs => erw [heye]
  apply h.trans
  have h_gt : j₀ < i₀ := by
    obtain h | h | h := lt_trichotomy j₀ i₀
    · exact h
    · exact (h_eq h.symm).elim
    · exact absurd h h_lt
  apply (Finset.sum_eq_single ⟨j₀, hj₀⟩ _ _).trans _
  ·
    intro k _ hk
    have hqk := GetShiftMatrix.eq.Ite (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩ i k
    have hpk := GetShiftMatrix.eq.Ite (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩ k j
    simp only [GetElem.getElem] at hqk hpk ⊢
    simp only [hqk, hpk]
    simp only [id, Nat.Delta.eq.Ite, ← Fin.val_eq_val]
    have hkn : (k : ℕ) ≠ j₀ := fun h => hk (Fin.ext (by simp; exact h))
    split_ifs <;> first
      | rfl
      | apply Tensor.EqMul_1.nat
      | apply Tensor.EqMul_0'0.nat
      | apply Tensor.EqMul0_0.nat
      | exact (Tensor.EqMul_0'0.nat _).trans Nat.cast_zero.symm
      | exact (Tensor.EqMul0_0.nat _).trans Nat.cast_zero.symm
      | exfalso; omega
  ·
    intro h
    exact (h (Finset.mem_univ _)).elim
  ·
    have hqk := GetShiftMatrix.eq.Ite (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩ i ⟨j₀, hj₀⟩
    have hpk := GetShiftMatrix.eq.Ite (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩ ⟨j₀, hj₀⟩ j
    simp only [GetElem.getElem] at hqk hpk ⊢
    simp only [hqk, hpk]
    simp only [id, Nat.Delta.eq.Ite, ← Fin.val_eq_val]
    split_ifs <;> first
      | rfl
      | apply Tensor.EqMul_1.nat
      | apply Tensor.EqMul_0'0.nat
      | apply Tensor.EqMul0_0.nat
      | exact (Tensor.EqMul_0'0.nat _).trans Nat.cast_zero.symm
      | exact (Tensor.EqMul0_0.nat _).trans Nat.cast_zero.symm
      | exfalso; omega


private lemma eye_cell_gt_mid
  [Semiring α] [CharZero α]
  (n i₀ j₀ : ℕ) (hi₀ : i₀ < n) (hj₀ : j₀ < n)
  (i j : Fin n)
  (h_eq : ¬ i₀ = j₀)
  (h_lt : ¬ i₀ < j₀)
  (hi0 : (i : ℕ) ≠ i₀)
  (hi1 : j₀ ≤ (i : ℕ) ∧ (i : ℕ) < i₀) :
  (((ShiftMatrix (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩) @
      ShiftMatrix (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩).get i).get j =
    ((eye (α := α) n).get i).get j := by
  have h := GetDot.eq.Sum_MulGetS
    (ShiftMatrix (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩)
    (ShiftMatrix (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩) i j
  have heye := GetEye.eq.Delta.fin (α := α) i j
  conv_rhs => erw [heye]
  apply h.trans
  have h_gt : j₀ < i₀ := by
    obtain h | h | h := lt_trichotomy j₀ i₀
    · exact h
    · exact (h_eq h.symm).elim
    · exact absurd h h_lt
  apply (Finset.sum_eq_single ⟨(i : ℕ) + 1, by linarith [hi₀, hi1.2]⟩ _ _).trans _
  ·
    intro k _ hk
    have hqk := GetShiftMatrix.eq.Ite (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩ i k
    have hpk := GetShiftMatrix.eq.Ite (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩ k j
    simp only [GetElem.getElem] at hqk hpk ⊢
    simp only [hqk, hpk]
    simp only [id, Nat.Delta.eq.Ite, ← Fin.val_eq_val]
    have hkn : (k : ℕ) ≠ (i : ℕ) + 1 := fun h => hk (Fin.ext (by simp; exact h))
    split_ifs <;> first
      | rfl
      | apply Tensor.EqMul_1.nat
      | apply Tensor.EqMul_0'0.nat
      | apply Tensor.EqMul0_0.nat
      | exact (Tensor.EqMul_0'0.nat _).trans Nat.cast_zero.symm
      | exact (Tensor.EqMul0_0.nat _).trans Nat.cast_zero.symm
      | exfalso; omega
  ·
    intro h
    exact (h (Finset.mem_univ _)).elim
  ·
    have hqk := GetShiftMatrix.eq.Ite (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩ i ⟨(i : ℕ) + 1, by linarith [hi₀, hi1.2]⟩
    have hpk := GetShiftMatrix.eq.Ite (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩ ⟨(i : ℕ) + 1, by linarith [hi₀, hi1.2]⟩ j
    simp only [GetElem.getElem] at hqk hpk ⊢
    simp only [hqk, hpk]
    simp only [id, Nat.Delta.eq.Ite, ← Fin.val_eq_val]
    split_ifs <;> first
      | rfl
      | apply Tensor.EqMul_1.nat
      | apply Tensor.EqMul_0'0.nat
      | apply Tensor.EqMul0_0.nat
      | exact (Tensor.EqMul_0'0.nat _).trans Nat.cast_zero.symm
      | exact (Tensor.EqMul0_0.nat _).trans Nat.cast_zero.symm
      | exfalso; omega


private lemma eye_cell_gt_else
  [Semiring α] [CharZero α]
  (n i₀ j₀ : ℕ) (hi₀ : i₀ < n) (hj₀ : j₀ < n)
  (i j : Fin n)
  (h_eq : ¬ i₀ = j₀)
  (h_lt : ¬ i₀ < j₀)
  (hi0 : (i : ℕ) ≠ i₀)
  (hi1 : ¬ (j₀ ≤ (i : ℕ) ∧ (i : ℕ) < i₀)) :
  (((ShiftMatrix (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩) @
      ShiftMatrix (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩).get i).get j =
    ((eye (α := α) n).get i).get j := by
  have h := GetDot.eq.Sum_MulGetS
    (ShiftMatrix (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩)
    (ShiftMatrix (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩) i j
  have heye := GetEye.eq.Delta.fin (α := α) i j
  conv_rhs => erw [heye]
  apply h.trans
  have h_gt : j₀ < i₀ := by
    obtain h | h | h := lt_trichotomy j₀ i₀
    · exact h
    · exact (h_eq h.symm).elim
    · exact absurd h h_lt
  apply (Finset.sum_eq_single i _ _).trans _
  ·
    intro k _ hk
    have hqk := GetShiftMatrix.eq.Ite (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩ i k
    have hpk := GetShiftMatrix.eq.Ite (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩ k j
    simp only [GetElem.getElem] at hqk hpk ⊢
    simp only [hqk, hpk]
    simp only [id, Nat.Delta.eq.Ite, ← Fin.val_eq_val]
    have hkn : (k : ℕ) ≠ (i : ℕ) := fun h => hk (Fin.ext h)
    split_ifs <;> first
      | rfl
      | apply Tensor.EqMul_1.nat
      | apply Tensor.EqMul_0'0.nat
      | apply Tensor.EqMul0_0.nat
      | exact (Tensor.EqMul_0'0.nat _).trans Nat.cast_zero.symm
      | exact (Tensor.EqMul0_0.nat _).trans Nat.cast_zero.symm
      | exfalso; omega
  ·
    intro h
    exact (h (Finset.mem_univ _)).elim
  ·
    have hqk := GetShiftMatrix.eq.Ite (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩ i i
    have hpk := GetShiftMatrix.eq.Ite (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩ i j
    simp only [GetElem.getElem] at hqk hpk ⊢
    simp only [hqk, hpk]
    simp only [id, Nat.Delta.eq.Ite, ← Fin.val_eq_val]
    split_ifs <;> first
      | rfl
      | apply Tensor.EqMul_1.nat
      | apply Tensor.EqMul_0'0.nat
      | apply Tensor.EqMul0_0.nat
      | exact (Tensor.EqMul_0'0.nat _).trans Nat.cast_zero.symm
      | exact (Tensor.EqMul0_0.nat _).trans Nat.cast_zero.symm
      | exfalso; omega
private lemma eye_cell_lt
  [Semiring α] [CharZero α]
  (n i₀ j₀ : ℕ) (hi₀ : i₀ < n) (hj₀ : j₀ < n)
  (i j : Fin n)
  (h_eq : ¬ i₀ = j₀)
  (h_lt : i₀ < j₀) :
  (((ShiftMatrix (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩) @
      ShiftMatrix (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩).get i).get j =
    ((eye (α := α) n).get i).get j := by
  if hi0 : (i : ℕ) = i₀ then
    apply eye_cell_lt_i0 n i₀ j₀ hi₀ hj₀ i j h_eq h_lt hi0
  else
    if hi1 : i₀ < (i : ℕ) ∧ (i : ℕ) ≤ j₀ then
      apply eye_cell_lt_mid n i₀ j₀ hi₀ hj₀ i j h_eq h_lt hi0 hi1
    else
      apply eye_cell_lt_else n i₀ j₀ hi₀ hj₀ i j h_eq h_lt hi0 hi1


private lemma eye_cell_gt
  [Semiring α] [CharZero α]
  (n i₀ j₀ : ℕ) (hi₀ : i₀ < n) (hj₀ : j₀ < n)
  (i j : Fin n)
  (h_eq : ¬ i₀ = j₀)
  (h_lt : ¬ i₀ < j₀) :
  (((ShiftMatrix (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩) @
      ShiftMatrix (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩).get i).get j =
    ((eye (α := α) n).get i).get j := by
  if hi0 : (i : ℕ) = i₀ then
    apply eye_cell_gt_i0 n i₀ j₀ hi₀ hj₀ i j h_eq h_lt hi0
  else
    if hi1 : j₀ ≤ (i : ℕ) ∧ (i : ℕ) < i₀ then
      apply eye_cell_gt_mid n i₀ j₀ hi₀ hj₀ i j h_eq h_lt hi0 hi1
    else
      apply eye_cell_gt_else n i₀ j₀ hi₀ hj₀ i j h_eq h_lt hi0 hi1


private lemma eye_aux
  [Semiring α] [CharZero α]
  (n i₀ j₀ : ℕ) (hi₀ : i₀ < n) (hj₀ : j₀ < n) :
  (ShiftMatrix (α := α) ⟨j₀, hj₀⟩ ⟨i₀, hi₀⟩) @
    ShiftMatrix (α := α) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩ = eye n := by
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  if h_eq : i₀ = j₀ then
    apply eye_cell_eq n i₀ j₀ hi₀ hj₀ i j h_eq
  else
    if h_lt : i₀ < j₀ then
      apply eye_cell_lt n i₀ j₀ hi₀ hj₀ i j h_eq h_lt
    else
      apply eye_cell_gt n i₀ j₀ hi₀ hj₀ i j h_eq h_lt


@[path]
private lemma main
  [Semiring α] [CharZero α]
  {n : ℕ}
  (i₀ j₀ : Fin n) :
-- imply
  (ShiftMatrix (α := α) j₀ i₀) @ ShiftMatrix (α := α) i₀ j₀ = eye n :=
  eye_aux n (i₀ : ℕ) (j₀ : ℕ) i₀.isLt j₀.isLt


-- created on 2026-09-10
-- updated on 2026-09-13
