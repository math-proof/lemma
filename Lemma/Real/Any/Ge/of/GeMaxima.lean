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
  (h : Maxima S f ≥ M) :
-- imply
  ∃ x ∈ S, f x ≥ M := by
-- proof
  obtain ⟨x, hx, e⟩ := (h₁.image f).csSup_mem (h₀.image f)
  refine ⟨x, hx, ?_⟩
  rw [e]
  exact h


-- created on 2019-06-07
