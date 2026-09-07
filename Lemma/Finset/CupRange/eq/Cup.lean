import sympy.sets.sets
import sympy.Basic


@[main, comm]
private lemma main
-- given
  (n : ℕ)
  (f : ℕ → Set α) :
-- imply
  ⋃ k ∈ range n, f k = ⋃ k : Fin n, f k := by
-- proof
  ext x
  simp [Set.mem_iUnion, Finset.mem_range]
  constructor
  ·
    rintro ⟨k, hk, hx⟩
    use ⟨k, hk⟩
  ·
    rintro ⟨k, hx⟩
    use k.val, k.isLt


-- created on 2020-07-24
-- updated on 2026-09-07
