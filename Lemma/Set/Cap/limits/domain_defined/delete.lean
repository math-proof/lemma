import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f : ι → Set α} :
-- imply
  (⋂ i ∈ (Set.univ : Set ι), f i) = ⋂ i, f i := by
-- proof
  ext x
  simp


-- created on 2021-01-18
-- updated on 2026-10-26
