import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {S : Set ℝ}
  {f g : ℝ → ℝ}
-- given
  (h₀ : S.Nonempty)
  (h₁ : BddAbove (f '' S))
  (h : ∀ x ∈ S, f x ≥ g x) :
-- imply
  Maxima S f ≥ Maxima S g := by
-- proof
  apply csSup_le (h₀.image g)
  rintro _ ⟨x, hx, rfl⟩
  exact le_trans (h x hx) (le_csSup h₁ (Set.mem_image_of_mem f hx))


-- created on 2023-04-23
