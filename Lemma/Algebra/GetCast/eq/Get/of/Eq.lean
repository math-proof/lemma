import Lemma.Basic


@[main]
private lemma main
-- given
  (h : n = n')
  (v : List.Vector α n)
  (i : Fin n) :
-- imply
  have h : List.Vector α n = List.Vector α n' := by rw [h]
  (cast h v)[i] = v[i] := by
-- proof
  intro h
  simp_all
  simp [GetElem.getElem]
  simp [List.Vector.get]
  aesop


-- created on 2025-07-06
