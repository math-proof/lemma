import sympy.vector.Basic


@[main, fin, subst 1]
private lemma main
  [One α]
-- given
  (i : Fin n) :
-- imply
  (1 : List.Vector α n)[i] = 1 := by
-- proof
  simp [GetElem.getElem]
  erw [List.Vector.get_replicate]


-- created on 2025-09-23
-- updated on 2026-07-19
