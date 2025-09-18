import sympy.tensor.tensor


@[main]
private lemma main
-- given
  (v : Tensor α (n :: s))
  (i : Fin n) :
-- imply
  v.toVector[i] = v[i] := by
-- proof
  simp [GetElem.getElem]
  simp [Tensor.get]
  simp [GetElem.getElem]


@[main]
private lemma fin
-- given
  (v : Tensor α (n :: s))
  (i : Fin n) :
-- imply
  v.toVector.get i = v[i] := by
-- proof
  have := main v i
  simp [GetElem.getElem] at *
  assumption


-- created on 2025-05-23
