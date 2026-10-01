import Mathlib.Data.Matrix.Basic
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ} :
-- imply
  (Matrix.of fun i j : Fin n => (-1 : ℤ) ^ (j : ℕ) * ((i : ℕ).choose j : ℤ)) ^ 2 = 1 := by
-- proof
  have core : ∀ n i : ℕ, i ≤ n → ∑ k ∈ Finset.Ico i (n + 1), (n.choose k : ℤ) * (-1) ^ (k - i) * (k.choose i : ℤ) =
      if n = i then 1 else 0 := by
    intro n i h
    obtain ⟨d, rfl⟩ : ∃ d, n = i + d := ⟨n - i, by omega⟩
    rw [Finset.sum_Ico_eq_sum_range, show i + d + 1 - i = d + 1 by omega]
    have e : ∀ j ∈ Finset.range (d + 1), ((i + d).choose (i + j) : ℤ) * (-1) ^ (i + j - i) * ((i + j).choose i : ℤ) =
        ((i + d).choose i : ℤ) * ((-1) ^ j * (d.choose j : ℤ)) := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hc : (i + d).choose (i + j) * (i + j).choose i = (i + d).choose i * d.choose j := by
        rw [Nat.choose_mul (by omega), Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
      have hc' : ((i + d).choose (i + j) : ℤ) * ((i + j).choose i : ℤ) = ((i + d).choose i : ℤ) * (d.choose j : ℤ) := by
        exact_mod_cast hc
      rw [Nat.add_sub_cancel_left]
      linear_combination (-1 : ℤ) ^ j * hc'
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, Int.alternating_sum_range_choose]
    by_cases hd : d = 0
    · subst hd
      simp
    · rw [if_neg hd, if_neg (by omega), mul_zero]
  ext i j
  rw [sq, Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => (-1 : ℤ) ^ k * ((i : ℕ).choose k : ℤ) * ((-1) ^ (j : ℕ) * (k.choose (j : ℕ) : ℤ))) n]
  have hi := i.isLt
  have hif : (if i = j then (1 : ℤ) else 0) = if (i : ℕ) = (j : ℕ) then 1 else 0 := by
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (congrArg Fin.val h1) h2
    · exact absurd (Fin.ext h2) h1
    · rfl
  rw [hif]
  by_cases hji : (j : ℕ) ≤ i
  · rw [← core i j hji, ← Finset.sum_subset (s₁ := Finset.Ico (j : ℕ) (i + 1))
      (fun k hk => Finset.mem_range.mpr (by rw [Finset.mem_Ico] at hk; omega))]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hp : (-1 : ℤ) ^ k = (-1) ^ (k - j) * (-1) ^ (j : ℕ) := by
        rw [← pow_add, Nat.sub_add_cancel hk.1]
      have h2 : ((-1 : ℤ) ^ (j : ℕ)) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
      rw [hp]
      linear_combination ((-1 : ℤ) ^ (k - j) * ((i : ℕ).choose k : ℤ) * (k.choose (j : ℕ) : ℤ)) * h2
    · intro k _ hk'
      rw [Finset.mem_Ico] at hk'
      rcases lt_or_ge k j with hkj | hkj
      · rw [Nat.choose_eq_zero_of_lt hkj]
        simp
      · rw [Nat.choose_eq_zero_of_lt (show (i : ℕ) < k by omega)]
        simp
  · rw [if_neg (by omega)]
    apply Finset.sum_eq_zero
    intro k _
    rcases lt_or_ge k j with hkj | hkj
    · rw [Nat.choose_eq_zero_of_lt hkj]
      simp
    · rw [Nat.choose_eq_zero_of_lt (show (i : ℕ) < k by omega)]
      simp


-- created on 2023-08-27
