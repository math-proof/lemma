import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
  {M : ℝ}
-- given
  (h₀ : S.Nonempty)
  (h : ∀ x ∈ S, f x ≥ M) :
-- imply
  Minima S f ≥ M := by
-- proof
  exact le_csInf (h₀.image f) (Set.forall_mem_image.mpr fun x hx => h x hx)


-- created on 2026-09-27
