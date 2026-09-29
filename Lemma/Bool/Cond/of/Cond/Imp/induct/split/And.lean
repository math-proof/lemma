import sympy.Basic


@[main]
private lemma main
  {P : ℕ → α → Prop}
  {t : α → α}
-- given
  (h₀ : ∀ x, P 0 x)
  (h₁ : ∀ n x, P n x ∧ P n (t x) → P (n + 1) x) :
-- imply
  ∀ n x, P n x := by
-- proof
  intro n
  induction n with
  | zero =>
    exact h₀
  | succ n ih =>
    intro x
    exact h₁ n x ⟨ih x, ih (t x)⟩


-- created on 2026-09-27
