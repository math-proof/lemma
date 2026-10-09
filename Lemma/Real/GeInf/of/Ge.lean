import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {S : Set ℝ}
  {f g : ℝ → ℝ}
-- given
  (h₀ : S.Nonempty)
  (h₁ : BddBelow (g '' S))
  (h : ∀ x ∈ S, f x ≥ g x) :
-- imply
  sInf (f '' S) ≥ sInf (g '' S) := by
-- proof
  refine le_csInf (h₀.image f) fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := hy
  exact le_trans (csInf_le h₁ (Set.mem_image_of_mem g hx)) (h x hx)


-- created on 2023-04-22
-- updated on 2023-04-23
