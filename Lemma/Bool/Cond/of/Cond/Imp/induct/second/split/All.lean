import sympy.Basic


@[main]
private lemma main
  {p : ℕ → Prop}
  {n : ℕ}
-- given
  (h₀ : p 0)
  (h₁ : ∀ n, (∀ k < n, p k) → p n) :
-- imply
  p n := by
-- proof
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      exact h₀
    | succ n =>
      exact h₁ _ ih


-- created on 2026-09-27
