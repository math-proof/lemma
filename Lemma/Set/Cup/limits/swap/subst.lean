import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f : ι → κ → Set α} :
-- imply
  (⋃ i, ⋃ j, f i j) = ⋃ j, ⋃ i, f j i := by
-- proof
  ext x
  simp only [Set.mem_iUnion]


-- created on 2021-09-22
-- updated on 2026-10-26
