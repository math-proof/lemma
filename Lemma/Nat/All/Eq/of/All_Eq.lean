import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {f : ℤ → ℂ}
  {a : ℤ}
-- given
  (h : ∀ n ≥ a, f (n + 1) = f n) :
-- imply
  ∀ n ≥ a, f n = f a := by
-- proof
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = a + k := ⟨(n - a).toNat, by omega⟩
  clear hn
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show a + ((k + 1 : ℕ) : ℤ) = a + k + 1 by push_cast; ring, h _ (by omega), ih]


-- created on 2019-01-07
