import sympy.Basic


@[main]
private lemma main
-- given
  (h : n = n')
  (v : List.Vector α n)
  (i : Fin n) :
-- imply
  have h : List.Vector α n = List.Vector α n' := by rw [h]
  (cast h v)[i.val] = v[i.val] := by
-- proof
  intro h
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
  have h : List.Vector α n = List.Vector α n' := by rw [h]
  (cast h v).get i = v.get ⟨i, hi⟩ := by
-- proof
  intro h
  simp_all
  simp [List.Vector.get]
  aesop


-- created on 2025-07-06
