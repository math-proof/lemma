import sympy.Basic


@[main, comm 1]
private lemma main
  {x y : ℕ}
-- given
  (h : x ≤ y)
  (z : ℕ) :
-- imply
  x - z ≤ y - z :=
-- proof
  Nat.sub_le_sub_right h z


-- created on 2024-07-01
-- updated on 2025-10-16
