import sympy.vector.Basic


@[main, fin, subst 0]
private lemma main
  [Zero α]
-- given
  (i : Fin n) :
-- imply
  (0 : List.Vector α n)[i] = 0 := by
-- proof
  simp [GetElem.getElem]
  erw [List.Vector.get_replicate]


-- created on 2025-09-04
-- updated on 2026-07-19
