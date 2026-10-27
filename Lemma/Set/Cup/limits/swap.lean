import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f : ι → κ → Set α} :
-- imply
  (⋃ i, ⋃ j, f i j) = ⋃ j, ⋃ i, f i j := by
-- proof
  ext x
  simp [Set.mem_iUnion]
  exact exists_comm


-- created on 2023-11-18
-- updated on 2026-10-26
