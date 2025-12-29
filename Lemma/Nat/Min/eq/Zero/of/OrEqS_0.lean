import sympy.Basic


@[main, left]
private lemma main
  {n m : ℕ}
-- given
  (h : n = 0 ∨ m = 0) :
-- imply
  n ⊓ m = 0 := by
-- proof
  omega


-- created on 2025-08-04
