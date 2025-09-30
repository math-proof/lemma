import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
-- given
  (n : ℕ)
  (f : ℕ → Set α) :
-- imply
  ⋃ k ∈ range n, f k = ⋃ k ∈ Ico (0 : ℤ) (n : ℤ), f k.toNat := by
-- proof
  ext x
  simp [Set.mem_iUnion, Set.mem_Ico]
  constructor
  ·
    intro h
    let ⟨k, hk1, hk2⟩ := h
    use k
    aesop
  .
    aesop


-- created on 2025-09-30
