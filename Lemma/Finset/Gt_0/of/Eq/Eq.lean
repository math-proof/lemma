import sympy.sets.sets
import sympy.Basic


@[main]
private lemma catalan
  {C : ℕ → ℤ}
  {n : ℕ}
-- given
  (h₀ : C 0 = 1)
  (h₁ : ∀ n, C (n + 1) = ∑ k ∈ Finset.range (n + 1), C k * C (n - k)) :
-- imply
  C n > 0 := by
-- proof
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [h₀]; norm_num
    | succ m =>
      rw [h₁]
      apply Finset.sum_pos
      · intro k hk
        rw [Finset.mem_range] at hk
        exact mul_pos (ih k (by omega)) (ih (m - k) (by omega))
      · exact ⟨0, by simp⟩


-- created on 2020-10-18
