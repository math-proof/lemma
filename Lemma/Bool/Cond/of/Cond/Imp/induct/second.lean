import sympy.Basic


@[path]
private lemma main
  {f g : ℕ → ℝ}
  {n : ℕ}
-- given
  (h₀ : f 0 > g 0)
  (h₁ : ∀ k < n, f k > g k → f n > g n) :
-- imply
  f n > g n := by
-- proof
  cases n with
  | zero =>
    apply h₀
  | succ n =>
    apply h₁ 0 (by omega) h₀


-- created on 2026-10-11
-- updated on 2026-10-17
