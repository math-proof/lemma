import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {j i : Fin n}
-- given
  (h : j ≥ i) :
-- imply
  ⟨(j - i : ℤ).natAbs, by grind⟩ = j - i := by
-- proof
  grind [Fin.coe_sub_iff_le.mpr h]


-- created on 2026-09-17
-- updated on 2026-09-17
