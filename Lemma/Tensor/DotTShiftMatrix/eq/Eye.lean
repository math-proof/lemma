import Lemma.Fin.Sum_MulDeltaS.eq.Delta
import Lemma.Nat.Delta
import Lemma.Nat.Delta.eq.Ite
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqMul0_0
import Lemma.Tensor.EqMul_0'0
import Lemma.Tensor.EqMul_1
import Lemma.Tensor.GetDot.eq.Sum_MulGetS
import Lemma.Tensor.GetEye.eq.Delta
import Lemma.Tensor.GetShiftMatrix.eq.Ite
import sympy.matrices.expressions.permutation
open Nat Tensor
set_option maxHeartbeats 1000000


@[main]
private lemma main
  [Semiring α] [CharZero α]
  (n i₀ j₀ : ℕ) (hi₀ : i₀ < n) (hj₀ : j₀ < n) :
-- imply
  (ShiftMatrix (α := α) n j₀ i₀) @ ShiftMatrix (α := α) n i₀ j₀ = eye n := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  have h := GetDot.eq.Sum_MulGetS (ShiftMatrix (α := α) n j₀ i₀) (ShiftMatrix n i₀ j₀) i j
  have heye := GetEye.eq.Delta.fin (α := α) i j
  conv_rhs => erw [heye]
  apply h.trans
  by_cases h_eq : i₀ = j₀
  ·
    subst h_eq
    apply (Finset.sum_eq_single i ?_ ?_).trans ?_
    ·
      intro k _ hk
      have hqk := GetShiftMatrix.eq.Ite (α := α) n i₀ i₀ i k
      have hpk := GetShiftMatrix.eq.Ite (α := α) n i₀ i₀ k j
      simp only [GetElem.getElem] at hqk hpk ⊢
      simp only [hqk, hpk]
      simp only [id, Delta.eq.Ite, ← Fin.val_eq_val]
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
      have hqk := GetShiftMatrix.eq.Ite (α := α) n i₀ i₀ i i
      have hpk := GetShiftMatrix.eq.Ite (α := α) n i₀ i₀ i j
      simp only [GetElem.getElem] at hqk hpk ⊢
      simp only [hqk, hpk]
      simp only [id, Delta.eq.Ite, ← Fin.val_eq_val]
      simp
      split_ifs
      · apply Tensor.EqMul_1.nat
      · exact (Tensor.EqMul_0'0.nat _).trans Nat.cast_zero.symm
  ·
    by_cases h_lt : i₀ < j₀
    ·
      by_cases hi0 : (i : ℕ) = i₀
      ·
        apply (Finset.sum_eq_single ⟨j₀, hj₀⟩ ?_ ?_).trans ?_
        ·
          intro k _ hk
          have hqk := GetShiftMatrix.eq.Ite (α := α) n j₀ i₀ i k
          have hpk := GetShiftMatrix.eq.Ite (α := α) n i₀ j₀ k j
          simp only [GetElem.getElem] at hqk hpk ⊢
          simp only [hqk, hpk]
          simp only [id, Delta.eq.Ite, ← Fin.val_eq_val]
          have hkn : (k : ℕ) ≠ j₀ := fun h => hk (Fin.ext (by simp; exact h))
          simp [if_neg (show ¬ j₀ = i₀ by grind), if_neg (show ¬j₀ < i₀ by grind), if_neg (show ¬↑k = j₀ by grind), if_pos h_lt, if_neg (show ¬ i₀ = j₀ by grind)]
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
          have hqk := GetShiftMatrix.eq.Ite (α := α) n j₀ i₀ i ⟨j₀, hj₀⟩
          have hpk := GetShiftMatrix.eq.Ite (α := α) n i₀ j₀ ⟨j₀, hj₀⟩ j
          simp only [GetElem.getElem] at hqk hpk ⊢
          simp only [hqk, hpk]
          simp only [id, Delta.eq.Ite, ← Fin.val_eq_val]
          split_ifs <;> first
            | rfl
            | apply Tensor.EqMul_1.nat
            | apply Tensor.EqMul_0'0.nat
            | apply Tensor.EqMul0_0.nat
            | exact (Tensor.EqMul_0'0.nat _).trans Nat.cast_zero.symm
            | exact (Tensor.EqMul0_0.nat _).trans Nat.cast_zero.symm
            | exfalso; omega
      ·
        by_cases hi1 : i₀ < (i : ℕ) ∧ (i : ℕ) ≤ j₀
        ·
          have hik : (i : ℕ) - 1 < n := by omega
          apply (Finset.sum_eq_single ⟨(i : ℕ) - 1, hik⟩ ?_ ?_).trans ?_
          ·
            intro k _ hk
            have hqk := GetShiftMatrix.eq.Ite (α := α) n j₀ i₀ i k
            have hpk := GetShiftMatrix.eq.Ite (α := α) n i₀ j₀ k j
            simp only [GetElem.getElem] at hqk hpk ⊢
            simp only [hqk, hpk]
            simp only [id, Delta.eq.Ite, ← Fin.val_eq_val]
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
            have hqk := GetShiftMatrix.eq.Ite (α := α) n j₀ i₀ i ⟨(i : ℕ) - 1, hik⟩
            have hpk := GetShiftMatrix.eq.Ite (α := α) n i₀ j₀ ⟨(i : ℕ) - 1, hik⟩ j
            simp only [GetElem.getElem] at hqk hpk ⊢
            simp only [hqk, hpk]
            simp only [id, Delta.eq.Ite, ← Fin.val_eq_val]
            split_ifs <;> first
              | rfl
              | apply Tensor.EqMul_1.nat
              | apply Tensor.EqMul_0'0.nat
              | apply Tensor.EqMul0_0.nat
              | exact (Tensor.EqMul_0'0.nat _).trans Nat.cast_zero.symm
              | exact (Tensor.EqMul0_0.nat _).trans Nat.cast_zero.symm
              | exfalso; omega
        ·
          apply (Finset.sum_eq_single i ?_ ?_).trans ?_
          ·
            intro k _ hk
            have hqk := GetShiftMatrix.eq.Ite (α := α) n j₀ i₀ i k
            have hpk := GetShiftMatrix.eq.Ite (α := α) n i₀ j₀ k j
            simp only [GetElem.getElem] at hqk hpk ⊢
            simp only [hqk, hpk]
            simp only [id, Delta.eq.Ite, ← Fin.val_eq_val]
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
            have hqk := GetShiftMatrix.eq.Ite (α := α) n j₀ i₀ i i
            have hpk := GetShiftMatrix.eq.Ite (α := α) n i₀ j₀ i j
            simp only [GetElem.getElem] at hqk hpk ⊢
            simp only [hqk, hpk]
            simp only [id, Delta.eq.Ite, ← Fin.val_eq_val]
            split_ifs <;> first
              | rfl
              | apply Tensor.EqMul_1.nat
              | apply Tensor.EqMul_0'0.nat
              | apply Tensor.EqMul0_0.nat
              | exact (Tensor.EqMul_0'0.nat _).trans Nat.cast_zero.symm
              | exact (Tensor.EqMul0_0.nat _).trans Nat.cast_zero.symm
              | exfalso; omega
    ·
      have h_gt : j₀ < i₀ := by
        rcases lt_trichotomy j₀ i₀ with h | h | h
        · exact h
        · exact (h_eq h.symm).elim
        · exact absurd h h_lt
      by_cases hi0 : (i : ℕ) = i₀
      ·
        apply (Finset.sum_eq_single ⟨j₀, hj₀⟩ ?_ ?_).trans ?_
        ·
          intro k _ hk
          have hqk := GetShiftMatrix.eq.Ite (α := α) n j₀ i₀ i k
          have hpk := GetShiftMatrix.eq.Ite (α := α) n i₀ j₀ k j
          simp only [GetElem.getElem] at hqk hpk ⊢
          simp only [hqk, hpk]
          simp only [id, Delta.eq.Ite, ← Fin.val_eq_val]
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
          have hqk := GetShiftMatrix.eq.Ite (α := α) n j₀ i₀ i ⟨j₀, hj₀⟩
          have hpk := GetShiftMatrix.eq.Ite (α := α) n i₀ j₀ ⟨j₀, hj₀⟩ j
          simp only [GetElem.getElem] at hqk hpk ⊢
          simp only [hqk, hpk]
          simp only [id, Delta.eq.Ite, ← Fin.val_eq_val]
          split_ifs <;> first
            | rfl
            | apply Tensor.EqMul_1.nat
            | apply Tensor.EqMul_0'0.nat
            | apply Tensor.EqMul0_0.nat
            | exact (Tensor.EqMul_0'0.nat _).trans Nat.cast_zero.symm
            | exact (Tensor.EqMul0_0.nat _).trans Nat.cast_zero.symm
            | exfalso; omega
      ·
        by_cases hi1 : j₀ ≤ (i : ℕ) ∧ (i : ℕ) < i₀
        ·
          have hik : (i : ℕ) + 1 < n := by linarith [hi₀, hi1.2]
          apply (Finset.sum_eq_single ⟨(i : ℕ) + 1, hik⟩ ?_ ?_).trans ?_
          ·
            intro k _ hk
            have hqk := GetShiftMatrix.eq.Ite (α := α) n j₀ i₀ i k
            have hpk := GetShiftMatrix.eq.Ite (α := α) n i₀ j₀ k j
            simp only [GetElem.getElem] at hqk hpk ⊢
            simp only [hqk, hpk]
            simp only [id, Delta.eq.Ite, ← Fin.val_eq_val]
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
            have hqk := GetShiftMatrix.eq.Ite (α := α) n j₀ i₀ i ⟨(i : ℕ) + 1, hik⟩
            have hpk := GetShiftMatrix.eq.Ite (α := α) n i₀ j₀ ⟨(i : ℕ) + 1, hik⟩ j
            simp only [GetElem.getElem] at hqk hpk ⊢
            simp only [hqk, hpk]
            simp only [id, Delta.eq.Ite, ← Fin.val_eq_val]
            split_ifs <;> first
              | rfl
              | apply Tensor.EqMul_1.nat
              | apply Tensor.EqMul_0'0.nat
              | apply Tensor.EqMul0_0.nat
              | exact (Tensor.EqMul_0'0.nat _).trans Nat.cast_zero.symm
              | exact (Tensor.EqMul0_0.nat _).trans Nat.cast_zero.symm
              | exfalso; omega
        ·
          apply (Finset.sum_eq_single i ?_ ?_).trans ?_
          ·
            intro k _ hk
            have hqk := GetShiftMatrix.eq.Ite (α := α) n j₀ i₀ i k
            have hpk := GetShiftMatrix.eq.Ite (α := α) n i₀ j₀ k j
            simp only [GetElem.getElem] at hqk hpk ⊢
            simp only [hqk, hpk]
            simp only [id, Delta.eq.Ite, ← Fin.val_eq_val]
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
            have hqk := GetShiftMatrix.eq.Ite (α := α) n j₀ i₀ i i
            have hpk := GetShiftMatrix.eq.Ite (α := α) n i₀ j₀ i j
            simp only [GetElem.getElem] at hqk hpk ⊢
            simp only [hqk, hpk]
            simp only [id, Delta.eq.Ite, ← Fin.val_eq_val]
            split_ifs <;> first
              | rfl
              | apply Tensor.EqMul_1.nat
              | apply Tensor.EqMul_0'0.nat
              | apply Tensor.EqMul0_0.nat
              | exact (Tensor.EqMul_0'0.nat _).trans Nat.cast_zero.symm
              | exact (Tensor.EqMul0_0.nat _).trans Nat.cast_zero.symm
              | exfalso; omega


-- created on 2026-09-10
