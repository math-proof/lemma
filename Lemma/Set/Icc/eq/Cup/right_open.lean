import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  (a b : ℤ) :
-- imply
  Set.Ico a b = ⋃ k ∈ Finset.Ico a b, Set.Ico k (k + 1) := by
-- proof
  rw [eq_comm]
  ext x
  simp only [Set.mem_iUnion, Finset.mem_Ico, Set.mem_Ico]
  constructor
  · rintro ⟨k, ⟨hka, hkb⟩, hk1, hk2⟩
    exact ⟨by omega, by omega⟩
  · rintro ⟨hax, hxb⟩
    exact ⟨x, ⟨hax, hxb⟩, le_rfl, by omega⟩


-- created on 2021-04-29
