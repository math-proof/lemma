import sympy.Basic


@[path]
private lemma main :
-- imply
  ⋃ k : ℕ, Set.Ico (-(k : ℤ) - 1) (-(k : ℤ)) = Set.Iio 0 := by
-- proof
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ico, Set.mem_Iio]
  constructor
  · rintro ⟨k, _, hk⟩
    omega
  · intro hx
    have h : 0 ≤ -x - 1 := by omega
    refine ⟨(-x - 1).toNat, ?_, by omega⟩
    rw [Int.toNat_of_nonneg h]
    omega


-- created on 2021-02-17
-- updated on 2023-05-14
