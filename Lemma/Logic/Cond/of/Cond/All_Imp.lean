import Lemma.Basic


@[main]
private lemma main
  {f : ℕ → Prop}
-- given
  (n : ℕ)
  (h₀ : f 0)
  (h₁ : ∀ n, f n → f (n + 1)) :
-- imply
  f n := by
-- proof
  induction n with
  | zero =>
    assumption
  | succ k ih =>
    apply h₁ k
    assumption


-- created on 2025-07-20
