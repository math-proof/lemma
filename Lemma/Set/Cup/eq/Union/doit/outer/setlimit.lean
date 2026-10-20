import sympy.Basic


@[path]
private lemma main
  {s : Set ι} [DecidablePred (· ∈ s)]
  {f : ι → Set α} :
-- imply
  (⋃ i ∈ s, f i) = ⋃ i, if i ∈ s then f i else ∅ := by
-- proof
  ext x
  simp


-- created on 2021-02-08
-- updated on 2026-10-17
