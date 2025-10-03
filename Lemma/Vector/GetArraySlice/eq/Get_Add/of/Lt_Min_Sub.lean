import sympy.vector.vector
import Lemma.Vector.GetTake.eq.Get.of.Lt_Min
import Lemma.Vector.GetDrop.eq.Get_Add.of.Lt_Sub
import Lemma.Algebra.Lt.of.Lt_Min
open Algebra Vector


@[main]
private lemma main
-- given
  (h : j < n ⊓ (N - i))
  (v : List.Vector α N) :
-- imply
  (v.array_slice i n)[j] = v[i + j] := by
-- proof
  simp [List.Vector.array_slice]
  simp only [GetTake.eq.Get.of.Lt_Min h]
  simp [GetElem.getElem]
  have := Lt.of.Lt_Min h
  have := GetDrop.eq.Get_Add.of.Lt_Sub this v
  simp [GetElem.getElem] at this
  assumption


-- created on 2025-05-31
-- updated on 2025-07-11
