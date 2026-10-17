import sympy.Basic


@[path]
private lemma main
  {f : ι → κ → Set α} :
-- imply
  (⋂ p : ι × κ, f p.1 p.2) = ⋂ i, ⋂ j, f i j := by
-- proof
  ext x
  simp


-- created on 2026-10-11
-- updated on 2026-10-17
