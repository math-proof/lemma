import sympy.functions.combinatorial.integer_factorials
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n i m : ℕ}
-- given
  (h₀ : n ≥ 1)
  (h₁ : i ≤ m + 1) :
-- imply
  ∑ k ∈ Finset.Ico i (m + 1), (n.choose k : ℤ) * (-1) ^ k = ((n - 1).choose m : ℤ) * (-1) ^ m + Binomial (n - 1) ((i : ℤ) - 1) * (-1) ^ i := by
-- proof
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  induction m with
  | zero =>
    interval_cases i <;> simp [Binomial]
  | succ m ih =>
    by_cases hi : i ≤ m + 1
    · rw [Finset.sum_Ico_succ_top (by omega), ih hi, Nat.choose_succ_succ]
      push_cast
      ring
    · have hi' : i = m + 2 := by omega
      subst hi'
      have hb : Binomial n ((↑(m + 2) : ℤ) - 1) = (n.choose (m + 1) : ℤ) := by
        simp only [Binomial]
        rw [if_pos (by omega)]
        congr 2
        omega
      rw [hb, Finset.Ico_self, Finset.sum_empty]
      ring


-- created on 2023-04-21
