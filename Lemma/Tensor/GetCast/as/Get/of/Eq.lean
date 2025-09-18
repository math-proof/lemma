import stdlib.SEq
import sympy.tensor.Basic


@[main]
private lemma main
-- given
  (h : s = s')
  (v : List.Vector (Tensor α s) n)
  (i : Fin n) :
-- imply
  have h : List.Vector (Tensor α s) n = List.Vector (Tensor α s') n := by rw [h]
  (cast h v)[i] ≃ v[i] := by
-- proof
  intro h
  constructor
  ·
    simp_all
  ·
    simp [GetElem.getElem]
    simp [List.Vector.get]
    aesop


-- created on 2025-06-29
-- updated on 2025-07-04
