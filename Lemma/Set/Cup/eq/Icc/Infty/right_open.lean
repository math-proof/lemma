import sympy.Basic


@[path]
private lemma main :
-- imply
  ⋃ k : ℕ, Set.Ico (k : ℤ) ((k : ℤ) + 1) = Set.Ici 0 := by
-- proof
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ico, Set.mem_Ici]
  constructor
  · rintro ⟨k, hk, _⟩
    omega
  · intro hx
    refine ⟨x.toNat, ?_, by omega⟩
    rw [Int.toNat_of_nonneg hx]


-- created on 2021-02-14
-- updated on 2023-05-14
