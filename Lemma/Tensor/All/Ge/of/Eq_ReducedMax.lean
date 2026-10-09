import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
  {M : ℝ}
-- given
  (h₀ : BddAbove (f '' S))
  (h : M = sSup (⋃ x ∈ S, ({f x} : Set ℝ))) :
-- imply
  ∀ x ∈ S, M ≥ f x := by
-- proof
  rw [← Set.image_eq_iUnion] at h
  intro x hx
  rw [h]
  exact le_csSup h₀ (Set.mem_image_of_mem f hx)


-- created on 2019-01-14
