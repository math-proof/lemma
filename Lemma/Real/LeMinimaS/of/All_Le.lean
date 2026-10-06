import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {α : Type*}
  {S : Set α}
  {f g : α → ℝ}
-- given
  (h₀ : S.Nonempty)
  (hB : BddBelow (f '' S))
  (h : ∀ x ∈ S, f x ≤ g x) :
-- imply
  Minima S f ≤ Minima S g := by
-- proof
  apply le_csInf (h₀.image g)
  rintro z ⟨x, hx, rfl⟩
  exact le_trans (csInf_le hB (Set.mem_image_of_mem f hx)) (h x hx)


-- created on 2023-04-23
