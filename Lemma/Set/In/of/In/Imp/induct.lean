import sympy.Basic


@[path]
private lemma main
  {f : ℕ → α}
  {g : ℕ → Set α}
  {n : ℕ}
-- given
  (h₀ : f 0 ∈ g 0)
  (h₁ : ∀ n : ℕ, f n ∈ g n → f (n + 1) ∈ g (n + 1)) :
-- imply
  f n ∈ g n := by
-- proof
  induction n with
  | zero => exact h₀
  | succ n ih => exact h₁ n ih


-- created on 2021-03-15
