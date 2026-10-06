import sympy.Basic


@[main]
private lemma main
  (a b : ℤ)
-- given
  (ha : a < 0)
  (hb : 0 ≤ b) :
-- imply
  ⋃ k ∈ Finset.Ico a b, Set.Ico k (k + 1) = Set.Ico a b := by
-- proof
  ext x
  simp only [Set.mem_iUnion, Finset.mem_Ico, Set.mem_Ico]
  constructor
  · rintro ⟨k, ⟨hka, hkb⟩, hk1, hk2⟩
    exact ⟨by omega, by omega⟩
  · rintro ⟨hax, hxb⟩
    exact ⟨x, ⟨hax, hxb⟩, le_rfl, by omega⟩


-- created on 2021-02-21
-- updated on 2023-05-20
