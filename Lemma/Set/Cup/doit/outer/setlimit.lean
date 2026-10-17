import sympy.Basic


@[path]
private lemma main
  {s : Set ι}
  {f g : ι → Set α} :
-- imply
  (⋃ i ∈ s, (f i ∪ g i)) = (⋃ i ∈ s, f i) ∪ (⋃ i ∈ s, g i) := by
-- proof
  ext x
  simp
  grind


-- created on 2026-10-11
-- updated on 2026-10-17
