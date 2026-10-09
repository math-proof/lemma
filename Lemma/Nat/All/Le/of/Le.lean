import sympy.sets.sets
import sympy.Basic


@[path]
private lemma monotone
  {a : ℤ → ℝ}
-- given
  (h : ∀ n, a (n + 1) ≤ a n)
  (N : ℤ) :
-- imply
  ∀ n ≥ N, a n ≤ a N := by
-- proof
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = N + k := ⟨(n - N).toNat, by omega⟩
  clear hn
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show N + ((k + 1 : ℕ) : ℤ) = N + k + 1 by push_cast; ring]
    exact le_trans (h _) ih


-- created on 2019-10-29
