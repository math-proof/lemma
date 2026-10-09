import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {α : Type*}
  {A B C : Set α}
-- given
  (hs : C ⊆ A)
  (h : A \ C = B \ C) :
-- imply
  A = B ∪ C := by
-- proof
  have h₁ : A = (A \ C) ∪ C := by
    ext z
    simp only [Set.mem_union, Set.mem_sdiff]
    constructor
    · intro hz
      if hc : z ∈ C then
        exact Or.inr hc
      else
        exact Or.inl ⟨hz, hc⟩
    · rintro (h | h)
      · exact h.1
      · exact hs h
  rw [h₁, h]
  ext z
  simp only [Set.mem_union, Set.mem_sdiff]
  tauto


-- created on 2021-03-31
