import sympy.Basic


@[main]
private lemma induct
  {f g : ℕ → ℝ → ℝ}
-- given
  (h₀ : ∀ x, f 0 x = g 0 x)
  (h₁ : ∀ n x, f n x = g n x ∧ f n (x + 1) = g n (x + 1) → f (n + 1) x = g (n + 1) x) :
-- imply
  ∀ n x, f n x = g n x ∧ f n (x + 1) = g n (x + 1) := by
-- proof
  intro n
  induction n with
  | zero =>
    intro x
    exact ⟨h₀ x, h₀ (x + 1)⟩
  | succ n ih =>
    intro x
    exact ⟨h₁ n x (ih x), h₁ n (x + 1) (ih (x + 1))⟩


-- created on 2019-04-17
