import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {M : ℝ}
  {S : Set ℝ}
  {f : ℝ → ℝ}
-- given
  (h₀ : S.Nonempty)
  (h : ∀ x ∈ S, f x ≤ M) :
-- imply
  Maxima S f ≤ M := by
-- proof
  exact csSup_le (h₀.image f) (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)


-- created on 2019-01-01
