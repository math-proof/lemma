import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Set ℝ}
  {f g : ℝ → ℝ}
-- given
  (h₀ : S.Nonempty)
  (h₁ : BddBelow (f '' S))
  (h : ∀ x ∈ S, f x ≤ g x) :
-- imply
  sInf (f '' S) ≤ sInf (g '' S) := by
-- proof
  have hlb : ∀ z ∈ g '' S, sInf (f '' S) ≤ z := by
    rintro _ ⟨x, hx, rfl⟩
    exact le_trans (csInf_le h₁ (Set.mem_image_of_mem f hx)) (h x hx)
  exact le_csInf (h₀.image g) hlb


-- created on 2023-04-23
