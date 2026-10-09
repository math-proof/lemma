import sympy.Basic


@[path]
private lemma induct.second
  {P : ℕ → Prop}
-- given
  (h₀ : P 0)
  (h₁ : ∀ n > 0, (∀ k < n, P k) → P n) :
-- imply
  ∀ n, P n := by
-- proof
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    ·
      exact h₀
    ·
      exact h₁ n hn ih


-- created on 2026-09-27
