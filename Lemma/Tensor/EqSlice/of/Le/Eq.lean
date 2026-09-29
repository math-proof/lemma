import sympy.Basic


@[main]
private lemma main
  {k n d : ℕ}
  {x y : ℕ → ℝ}
-- given
  (_h₀ : k ≤ n)
  (h₁ : x = y) :
-- imply
  (fun i : Fin ((k + d - 1) / d) => x (i * d)) = fun i : Fin ((k + d - 1) / d) => y (i * d) := by
-- proof
  rw [h₁]


-- created on 2026-09-27
