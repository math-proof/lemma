import sympy.Basic


@[path]
private lemma main
  {x y z : ℕ}
-- given
  (h : x ≤ y) :
-- imply
  x ≤ y + z := by
-- proof
  exact h.trans (Nat.le_add_right y z)


-- created on 2019-10-24
