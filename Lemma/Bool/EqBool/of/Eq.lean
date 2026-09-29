import sympy.Basic


@[main]
private lemma main
  [Zero α] [DecidableEq α]
  {x y : α}
-- given
  (h : x = y) :
-- imply
  Bool.toNat (x ≠ 0) = Bool.toNat (y ≠ 0) := by
-- proof
  rw [h]


-- created on 2026-09-27
