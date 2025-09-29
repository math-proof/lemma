import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
-- given
  (h : n = m)
  (a : List.Vector α n)
  (b : List.Vector α m) :
-- imply
  HEq a b ↔ HEq a.val b.val := by
-- proof
  apply Subtype.heq_iff_coe_heq
  .
    rfl
  .
    rw [h]


-- created on 2025-08-02
