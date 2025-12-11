import sympy.Basic


@[main]
private lemma main
  [GroupWithZero α]
  {a : α}
-- given
  (h : a ≠ 0) :
-- imply
  a⁻¹ ≠ 0 := by
-- proof
  contrapose! h
  simp_all


-- created on 2025-12-11
