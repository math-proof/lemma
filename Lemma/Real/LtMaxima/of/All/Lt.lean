import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma given
  {M : ℝ}
  {S : Set ℝ}
  {f : ℝ → ℝ}
-- given
  (h₀ : S.Finite)
  (h₁ : S.Nonempty)
  (h : ∀ x ∈ S, f x < M) :
-- imply
  Maxima S f < M := by
-- proof
  obtain ⟨x, hx, e⟩ := (h₁.image f).csSup_mem (h₀.image f)
  show sSup (f '' S) < M
  rw [← e]
  exact h x hx


-- created on 2023-11-12
