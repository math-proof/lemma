import sympy.Basic


@[path]
private lemma main
  {f : ℤ → Set α} :
-- imply
  (⋂ i, f i) = ⋂ i, f (-i) := by
-- proof
  ext x
  simp only [Set.mem_iInter]
  exact ⟨fun h i => by simpa using h (-i), fun h i => by simpa using h (-i)⟩


-- created on 2026-10-11
-- updated on 2026-10-17
