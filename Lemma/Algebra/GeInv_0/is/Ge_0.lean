import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  (a : α) :
-- imply
  a⁻¹ ≥ 0 ↔ a ≥ 0 :=
-- proof
  inv_nonneg


-- created on 2025-01-14
