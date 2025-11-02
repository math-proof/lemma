import sympy.Basic


@[main]
private lemma main
-- given
  (h : n = n')
  (v : List.Vector α n)
  (i : Fin n) :
-- imply
  (cast (congrArg (List.Vector α) h) v)[i.val] = v[i.val] := by
-- proof
  simp [GetElem.getElem]
  simp [List.Vector.get]
  aesop


@[main]
private lemma fin
-- given
  (h : n = n')
  (v : List.Vector α n)
  (i : Fin n') :
-- imply
  have hi : i < n' := by simp
  have hi : i < n := by
    simp [h.symm] at hi
    assumption
  (cast (congrArg (List.Vector α) h) v).get i = v.get ⟨i, hi⟩ := by
-- proof
  simp_all
  simp [List.Vector.get]
  aesop


-- created on 2025-07-06
