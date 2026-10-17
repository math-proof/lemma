import sympy.Basic


@[path]
private lemma main
  {f : ι → κ → Set α} :
-- imply
  (⋃ i, ⋃ j, f i j) = ⋃ j, ⋃ i, f j i := by
-- proof
  ext x
  simp only [Set.mem_iUnion]


-- created on 2026-10-11
-- updated on 2026-10-17
