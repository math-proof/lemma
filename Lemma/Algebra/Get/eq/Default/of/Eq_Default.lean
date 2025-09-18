import stdlib.List.Vector
import Lemma.Basic


@[main]
private lemma main
  [Inhabited α]
  {i : Fin n}
  {v : List.Vector α n}
-- given
  (h : v = default) :
-- imply
  v[i] = default := by
-- proof
  rw [h]
  simp [Inhabited.default]
  simp [GetElem.getElem]


-- created on 2025-05-09
