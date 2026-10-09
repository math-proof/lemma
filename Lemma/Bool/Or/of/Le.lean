import sympy.Basic


@[path]
private lemma main
  [LinearOrder α]
  {x y : α}
-- given
  (h : x ≤ y) :
-- imply
  x < y ∨ x = y :=
-- proof
  lt_or_eq_of_le h


@[path]
private lemma split
  [LinearOrder α]
  {x a : α}
-- given
  (h : x ≤ a)
  (z : α) :
-- imply
  (x ≤ a ∧ x ≥ z) ∨ x < z := by
-- proof
  by_cases hz : x < z
  ·
    exact Or.inr hz
  ·
    exact Or.inl ⟨h, not_lt.mp hz⟩


-- created on 2021-08-10
