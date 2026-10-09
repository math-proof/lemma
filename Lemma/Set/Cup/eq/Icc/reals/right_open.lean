import sympy.Basic


@[path]
private lemma main :
-- imply
  ⋃ k : ℤ, Set.Ico k (k + 1) = (Set.univ : Set ℤ) := by
-- proof
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ico, Set.mem_univ, iff_true]
  exact ⟨x, by omega⟩


-- created on 2021-02-18
-- updated on 2023-05-13
