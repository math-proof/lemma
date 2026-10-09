import sympy.Basic


@[path]
private lemma main :
-- imply
  ⋃ k : ℕ, Set.Ioc (k : ℤ) ((k : ℤ) + 1) = Set.Ioi 0 := by
-- proof
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_Ioi]
  constructor
  · rintro ⟨k, hk, _⟩
    omega
  · intro hx
    have h : 0 ≤ x - 1 := by omega
    refine ⟨(x - 1).toNat, ?_, by omega⟩
    rw [Int.toNat_of_nonneg h]
    omega


-- created on 2021-02-13
-- updated on 2023-05-12
