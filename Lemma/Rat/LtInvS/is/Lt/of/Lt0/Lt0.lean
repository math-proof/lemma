import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [GroupWithZero G]
  [PartialOrder G]
  [PosMulReflectLT G]
  [MulPosReflectLT G]
  {a b : G}
-- given
  (ha : 0 < a)
  (hb : 0 < b) :
-- imply
  a⁻¹ < b⁻¹ ↔ b < a :=
-- proof
  inv_lt_inv₀ ha hb


-- created on 2025-12-08
