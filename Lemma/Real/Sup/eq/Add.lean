import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
  {h : ℝ}
-- given
  (h₀ : S.Nonempty)
  (h₁ : BddAbove (f '' S)) :
-- imply
  sSup ((fun x => f x + h) '' S) = sSup (f '' S) + h := by
-- proof
  have hne : ((fun x => f x + h) '' S).Nonempty := h₀.image _
  have hb : BddAbove ((fun x => f x + h) '' S) := by
    obtain ⟨b, hb⟩ := h₁
    refine ⟨b + h, fun z hz => ?_⟩
    obtain ⟨x, hx, rfl⟩ := hz
    have h₃ := add_le_add_right (hb (Set.mem_image_of_mem f hx)) h
    linarith
  apply le_antisymm
  · apply csSup_le hne
    rintro _ ⟨x, hx, rfl⟩
    have h₃ := add_le_add_right (le_csSup h₁ (Set.mem_image_of_mem f hx)) h
    linarith
  · have h₂ : ∀ z ∈ f '' S, z ≤ sSup ((fun x => f x + h) '' S) - h := by
      rintro _ ⟨x, hx, rfl⟩
      have h₃ : f x + h ≤ sSup ((fun x => f x + h) '' S) :=
        le_csSup hb (Set.mem_image_of_mem _ hx)
      linarith
    have h₃ := csSup_le (h₀.image f) h₂
    linarith


-- created on 2019-09-09
