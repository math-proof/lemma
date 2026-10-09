import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {M : ℝ}
  {S : Set ℝ}
  {f : ℝ → ℝ}
-- given
  (h₀ : S.Finite)
  (h₁ : S.Nonempty)
  (h : ∀ x ∈ S, f x > M) :
-- imply
  Minima S f > M := by
-- proof
  obtain ⟨x, hx, e⟩ := (h₁.image f).csInf_mem (h₀.image f)
  show M < sInf (f '' S)
  rw [← e]
  exact h x hx


-- created on 2019-12-01
