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
  (hB : BddAbove (f '' S))
  (h : Maxima S f ≤ M) :
-- imply
  ∀ x ∈ S, f x ≤ M := by
-- proof
  intro x hx
  exact (csSup_le_iff hB (h₀.image f)).mp h (f x) (Set.mem_image_of_mem f hx)


-- created on 2026-10-03
