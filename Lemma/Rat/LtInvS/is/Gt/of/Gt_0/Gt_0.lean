import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [GroupWithZero G]
  [PartialOrder G]
  [PosMulReflectLT G]
  [MulPosReflectLT G]
  {a b : G}
-- given
  (ha : a > 0)
  (hb : b > 0) :
-- imply
  a⁻¹ < b⁻¹ ↔ a > b :=
-- proof
  inv_lt_inv₀ ha hb


-- created on 2025-12-08
