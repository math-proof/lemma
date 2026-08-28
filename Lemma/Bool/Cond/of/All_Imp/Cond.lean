import sympy.Basic


@[main]
private lemma main
  {f : ℕ → Prop}
-- given
  (h₀ : f 0)
  (h₁ : ∀ n, f n → f (n + 1))
  (n : ℕ) :
-- imply
  f n := by
-- proof
  induction n with
  | zero =>
    assumption
  | succ k ih =>
    apply h₁ k
    assumption


-- created on 2018-04-18
