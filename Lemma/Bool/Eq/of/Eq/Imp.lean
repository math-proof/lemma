import sympy.Basic


@[main]
private lemma induct.double
  {f g : ℕ → ℝ → ℝ}
-- given
  (h₀ : ∀ z, f 0 z = g 0 z)
  (h₁ : ∀ n, (∀ x, f n x = g n x) → ∀ y, f (n + 1) y = g (n + 1) y) :
-- imply
  ∀ n x, f n x = g n x := by
-- proof
  intro n
  induction n with
  | zero =>
    exact h₀
  | succ n ih =>
    exact h₁ n ih


-- created on 2026-09-27
