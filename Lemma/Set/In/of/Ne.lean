import sympy.Basic


@[main]
private lemma main
  {x y : α}
-- given
  (h : x ≠ y) :
-- imply
  x ∈ Set.univ \ {y} := by
-- proof
  exact Set.mem_sdiff_singleton.mpr ⟨Set.mem_univ _, h⟩


-- created on 2021-09-11
