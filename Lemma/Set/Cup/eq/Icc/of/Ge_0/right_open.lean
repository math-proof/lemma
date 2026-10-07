import sympy.Basic


@[main]
private lemma main
  (n : ℤ)
-- given
  (_hn : 0 ≤ n) :
-- imply
  ⋃ k ∈ Finset.Ico (0 : ℤ) n, Set.Ico k (k + 1) = Set.Ico 0 n := by
-- proof
  ext x
  simp only [Set.mem_iUnion, Finset.mem_Ico, Set.mem_Ico]
  constructor
  · rintro ⟨k, ⟨_, hkb⟩, hk1, hk2⟩
    omega
  · rintro ⟨hax, hxb⟩
    exact ⟨x, ⟨hax, hxb⟩, le_rfl, by omega⟩


-- created on 2021-02-19
-- updated on 2023-05-20
