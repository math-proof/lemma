import sympy.Basic


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {n : ℤ} :
-- imply
  (⌊(n : α) / 2⌋ : α) = if n % 2 = 0 then (n : α) / 2 else ((n : α) - 1) / 2 := by
-- proof
  split_ifs with h
  ·
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    push_cast
    rw [mul_div_cancel_left₀ (k : α) two_ne_zero, Int.floor_intCast]
  ·
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    push_cast
    rw [show (2 * (k : α) + 1) / 2 = k + 1 / 2 by ring, show (2 * (k : α) + 1 - 1) / 2 = k by ring,
      Int.floor_intCast_add, Int.floor_eq_zero_iff.mpr (by norm_num)]
    simp


-- created on 2026-09-27
