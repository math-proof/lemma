import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
  {h : ℝ}
-- given
  (h₀ : S.Nonempty)
  (h₁ : BddBelow (f '' S)) :
-- imply
  sInf ((fun x => f x + h) '' S) = sInf (f '' S) + h := by
-- proof
  have hne : ((fun x => f x + h) '' S).Nonempty := h₀.image _
  have hb : BddBelow ((fun x => f x + h) '' S) := by
    obtain ⟨b, hb⟩ := h₁
    refine ⟨b + h, fun z hz => ?_⟩
    obtain ⟨x, hx, rfl⟩ := hz
    have h₃ := add_le_add_right (hb (Set.mem_image_of_mem f hx)) h
    linarith
  apply le_antisymm
  · have h₂ : sInf ((fun x => f x + h) '' S) - h ∈ lowerBounds (f '' S) := by
      rintro _ ⟨x, hx, rfl⟩
      have h₃ : sInf ((fun x => f x + h) '' S) ≤ f x + h :=
        csInf_le hb (Set.mem_image_of_mem _ hx)
      linarith
    have h₃ := le_csInf (h₀.image f) h₂
    linarith
  · apply le_csInf hne
    rintro _ ⟨x, hx, rfl⟩
    have h₃ := add_le_add_right (csInf_le h₁ (Set.mem_image_of_mem f hx)) h
    linarith


-- created on 2019-08-26
