import Lemma.Vector.ValAppend.eq.AppendValS
import Theorem.List.GetAppend.eq.Get_Sub_Length.of.GtLengthAppend.GeLength
open List Vector


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.GetAppend.eq.Get_Sub.of.Lt_Add.Ge |
| fin | Vector.GetAppend.eq.Get_Sub.of.Lt_Add.Ge.fin |
-/
@[path, fin]
private lemma main
-- given
  (h₀ : i ≥ m)
  (h₁ : i < m + n)
  (a : List.Vector α m)
  (b : List.Vector α n) :
-- imply
  (a ++ b)[i] = b[i - m] := by
-- proof
  simp [GetElem.getElem]
  simp [List.Vector.get]
  simp [ValAppend.eq.AppendValS]
  rw [GetAppend.eq.Get_Sub_Length.of.GtLengthAppend.GeLength (by simpa using h₀) (by simpa using h₁)]
  simp_all


-- created on 2025-05-31
-- updated on 2026-11-20
