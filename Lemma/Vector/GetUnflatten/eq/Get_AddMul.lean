import Lemma.Algebra.ValGetUnflatten.eq.ValArraySlice
import Lemma.Algebra.Lt_Sub.of.LtAdd
import Lemma.Vector.GetArraySlice.eq.Get_Add.of.Lt_Min_Sub
import Lemma.Algebra.AddMul.lt.Mul
open Algebra Vector


@[main, comm]
private lemma main
-- given
  (v : List.Vector α (m * n))
  (i : Fin m)
  (j : Fin n):
-- imply
  have := AddMul.lt.Mul i j
  v.unflatten[i, j] = v[i * n + j] := by
-- proof
  intro h
  simp [GetElem.getElem]
  have := ValGetUnflatten.eq.ValArraySlice v i
  simp [GetElem.getElem] at this
  simp only [List.Vector.get] at this
  simp at this
  simp only [List.Vector.get]
  simp
  simp only [this]
  apply GetArraySlice.eq.Get_Add.of.Lt_Min_Sub
  simp
  apply Lt_Sub.of.LtAdd.left.nat h


@[main, comm]
private lemma fin
-- given
  (v : List.Vector α (m * n))
  (i : Fin m)
  (j : Fin n):
-- imply
  have h_ij := AddMul.lt.Mul i j
  (v.unflatten.get i).get j = v.get ⟨i * n + j, h_ij⟩ := by
-- proof
  apply main


-- created on 2025-05-31
-- updated on 2025-07-09
