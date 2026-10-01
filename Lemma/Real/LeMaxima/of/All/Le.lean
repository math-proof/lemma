import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {S : Set ℝ}
  {f : ℝ → ℝ}
  {M : ℝ}
-- given
  (h₀ : S.Nonempty)
  (h : ∀ x ∈ S, f x ≤ M) :
-- imply
  Maxima S f ≤ M := by
-- proof
  exact csSup_le (h₀.image f) (Set.forall_mem_image.mpr fun x hx => h x hx)


-- created on 2019-01-01
