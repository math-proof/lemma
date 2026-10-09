import sympy.Basic


@[path]
private lemma main :
-- imply
  ⋃ k : ℤ, Set.Ioc k (k + 1) = (Set.univ : Set ℤ) := by
-- proof
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_univ, iff_true]
  exact ⟨x - 1, by omega⟩


-- created on 2021-02-18
