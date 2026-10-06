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
  (hB : BddBelow (f '' S))
  (h : ∀ x ∈ S, f x ≤ M) :
-- imply
  Minima S f ≤ M := by
-- proof
  obtain ⟨x, hx⟩ := h₀
  exact le_trans (csInf_le hB (Set.mem_image_of_mem f hx)) (h x hx)


-- created on 2023-03-25
