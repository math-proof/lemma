import stdlib.List.Vector
import Lemma.Algebra.ValGetUnflatten.eq.ValSubStr
import Lemma.Algebra.Ge.of.NotLt
import Lemma.Algebra.Get.eq.Default.of.AddMul.ge.Mul
import Lemma.Algebra.GetSubstr.eq.Get_Add
import Lemma.Algebra.Lt_Sub.of.LtAdd
open Algebra


@[main]
private lemma main
  [Inhabited α]
-- given
  (v : List.Vector α (m * n))
  (i : Fin m)
  (j : Fin n):
-- imply
  v[i * n + j] = v.unflatten[i, j] := by
-- proof
  simp [GetElem.getElem]
  split_ifs with h
  ·
    have := ValGetUnflatten.eq.ValSubStr v i
    simp [GetElem.getElem] at this
    simp only [List.Vector.get] at this
    simp at this
    simp only [List.Vector.get]
    simp
    simp only [this]
    apply Eq.symm
    have := GetSubstr.eq.Get_Add v (i * n) j
    simp [GetElem.getElem] at this
    simp [h] at this
    have h := Lt_Sub.of.LtAdd.nat.left h
    simp [h] at this
    assumption
  ·
    have h := Ge.of.NotLt h
    have := Get.eq.Default.of.AddMul.ge.Mul h v.unflatten
    apply Eq.symm
    simp [GetElem.getElem] at this
    assumption


-- created on 2025-05-07
-- updated on 2025-05-10
