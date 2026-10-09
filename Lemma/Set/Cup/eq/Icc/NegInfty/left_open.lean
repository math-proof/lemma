import sympy.Basic


@[path]
private lemma main :
-- imply
  ⋃ k : ℕ, Set.Ioc (-(k : ℤ) - 1) (-(k : ℤ)) = Set.Iic 0 := by
-- proof
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_Iic]
  constructor
  · rintro ⟨k, _, hk⟩
    omega
  · intro hx
    have h : 0 ≤ -x := by omega
    refine ⟨(-x).toNat, ?_, by omega⟩
    rw [Int.toNat_of_nonneg h]
    omega


-- created on 2021-02-16
-- updated on 2023-05-19
