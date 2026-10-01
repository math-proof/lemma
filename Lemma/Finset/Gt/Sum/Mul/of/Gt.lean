import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {f g : ℕ → ℝ}
-- given
  (h₀ : n > 0)
  (h : ∀ i, f i > g i) :
-- imply
  ∑ i ∈ Finset.range (n + 1), n * f i > ∑ i ∈ Finset.range (n + 1), n * g i := by
-- proof
  have hn : (0 : ℝ) < n := by exact_mod_cast h₀
  exact Finset.sum_lt_sum_of_nonempty ⟨0, by simp⟩ fun i _ => mul_lt_mul_of_pos_left (h i) hn


-- created on 2026-09-27
