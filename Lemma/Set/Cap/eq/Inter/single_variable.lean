import sympy.Basic


@[path]
private lemma main
  {s : Set ι}
  {g h : ι → Set α} :
-- imply
  (⋂ x ∈ s, g x ∩ h x) = (⋂ x ∈ s, g x) ∩ ⋂ x ∈ s, h x := by
-- proof
  ext y
  simp
  grind [Set.mem_iInter]


-- created on 2026-10-11
-- updated on 2026-10-17
