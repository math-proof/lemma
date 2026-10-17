import sympy.Basic


@[path]
private lemma main
  {s : Set ι}
  {t : Set κ}
  {f : ι → κ → Set α} :
-- imply
  (⋃ i ∈ s, ⋃ j ∈ t, f i j) = ⋃ j ∈ t, ⋃ i ∈ s, f i j := by
-- proof
  ext x
  simp
  grind


-- created on 2026-10-11
-- updated on 2026-10-17
