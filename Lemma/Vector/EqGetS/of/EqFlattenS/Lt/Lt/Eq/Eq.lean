import Lemma.Vector.EqUnflattenFlatten
import Lemma.Vector.GetUnflatten.eq.Get_AddMul.of.Lt.Lt
import Lemma.Vector.EqValS.of.SEq
open Vector


@[main]
private lemma main
  {X : List.Vector (List.Vector α n) m}
  {X' : List.Vector (List.Vector α n') m'}
-- given
  (h_n : n' = n)
  (h_m : m' = m)
  (h_i : i < m)
  (h_j : j < n)
  (h : X'.flatten ≃ X.flatten) :
-- imply
  have : i < m' := by rwa [h_m]
  have : j < n' := by rwa [h_n]
  X'[i, j] = X[i, j] := by
-- proof
  intro h_i h_j
  rw [← EqUnflattenFlatten X, ← EqUnflattenFlatten X']
  repeat rw [GetUnflatten.eq.Get_AddMul.of.Lt.Lt]
  simp [h_n]
  simp [GetElem.getElem]
  simp [List.Vector.get]
  simp [EqValS.of.SEq h]


-- created on 2025-07-09
