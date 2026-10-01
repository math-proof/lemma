import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n i : ℕ}
-- given
  (h : i ≤ n) :
-- imply
  ∑ k ∈ Finset.Ico i (n + 1), (n.choose k : ℤ) * (-1) ^ (k - i) * (k.choose i : ℤ) = if n = i then 1 else 0 := by
-- proof
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


-- created on 2026-09-27
