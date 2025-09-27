import Lemma.Basic


@[main]
private lemma Main'
-- given
  (s t u : Set α) :
-- imply
  (s \ t) ∪ u = (s ∪ u) \ (t \ u) := by
-- proof
  ext x
  simp only [Set.mem_union, Set.mem_diff]
  constructor
  · intro h
    cases h with
    | inl hs => exact ⟨Or.inl hs.left, fun h => hs.right h.left⟩
    | inr hu => exact ⟨Or.inr hu, fun h => h.right hu⟩
  · intro h
    rcases h with ⟨hsu, hnotin⟩
    cases hsu with
    | inl hs =>
      tauto
    | inr hu =>
      exact Or.inr hu



-- created on 2025-07-20
