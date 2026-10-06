import Lemma.Set.Ne.NotIn.of.NotIn_Union
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : α}
  {s : Set α} :
-- imply
  (x ≠ y ∧ x ∉ s) ↔ x ∉ s ∪ {y} := by
-- proof
  constructor
  · intro h
    apply Set.Ne.NotIn.of.NotIn_Union h.1 h.2
  · intro h
    have h₁ : x ∉ ({y} : Set α) := fun hy ↦ h (Set.mem_union_right s hy)
    have h₂ : x ∉ s := fun hs ↦ h (Set.mem_union_left {y} hs)
    exact ⟨fun he ↦ h₁ (he ▸ Set.mem_singleton y), h₂⟩


-- created on 2023-05-20
