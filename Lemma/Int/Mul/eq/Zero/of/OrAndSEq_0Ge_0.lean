import sympy.Basic


@[main]
private lemma main
  [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y : α}
-- given
  (h : x = 0 ∧ y ≥ 0 ∨ y = 0 ∧ x ≥ 0) :
-- imply
  x * y = 0 := by
-- proof
  obtain h | h := h <;>
  ·
    let ⟨h, _⟩ := h
    rw [h]
    simp


-- created on 2025-04-19
