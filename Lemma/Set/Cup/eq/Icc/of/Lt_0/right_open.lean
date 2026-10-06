import sympy.Basic


@[main]
private lemma main
  (n : ℤ)
-- given
  (hn : n < 0) :
-- imply
  ⋃ k ∈ Finset.Ico n 0, Set.Ico k (k + 1) = Set.Ico n 0 := by
-- proof
  ext x
  simp only [Set.mem_iUnion, Finset.mem_Ico, Set.mem_Ico]
  constructor
  · rintro ⟨k, ⟨hka, hkb⟩, hk1, hk2⟩
    exact ⟨by omega, by omega⟩
  · rintro ⟨hax, hxb⟩
    exact ⟨x, ⟨hax, hxb⟩, le_rfl, by omega⟩


-- created on 2021-02-20
-- updated on 2023-05-20
