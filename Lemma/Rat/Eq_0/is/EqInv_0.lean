import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [GroupWithZero α]
-- given
  (a : α) :
-- imply
  a = 0 ↔ a⁻¹ = 0 := by
-- proof
  simp_all


-- created on 2026-07-08
