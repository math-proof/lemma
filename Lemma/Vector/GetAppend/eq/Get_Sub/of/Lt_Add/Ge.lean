import Lemma.Vector.ValAppend.eq.AppendValS
import Lemma.List.GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength
open List Vector


@[main]
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
  rw [GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength (by simp_all) (by simp_all)]
  simp_all


-- created on 2025-05-31
