import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Set α}
  {f g : α → ℝ}
-- given
  (h₀ : S.Nonempty)
  (h₁ : BddAbove (g '' S))
  (h₂ : ∀ x ∈ S, f x ≤ g x) :
-- imply
  sSup (f '' S) ≤ sSup (g '' S) := by
-- proof
  apply csSup_le (h₀.image f)
  rintro _ ⟨x, hx, rfl⟩
  exact le_trans (h₂ x hx) (le_csSup h₁ (Set.mem_image_of_mem g hx))


-- created on 2023-04-23
