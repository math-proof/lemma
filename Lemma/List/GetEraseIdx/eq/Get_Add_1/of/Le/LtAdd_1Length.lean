import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength
import Lemma.List.GetDrop.eq.Get_Add.of.GtLength_Add
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h₀ : j + 1 < s.length)
  (h₁ : i ≤ j) :
-- imply
  (s.eraseIdx i)[j]'(by grind) = s[j + 1] := by
-- proof
  simp [EraseIdx.eq.Append_Drop_Add_1]
  rw [GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength]
  ·
    rw [GetDrop.eq.Get_Add.of.GtLength_Add]
    .
      simp
      simp only [GetElem.getElem]
      apply congrArg
      simp
      omega
    .
      simp
      omega
  ·
    simp
    left
    assumption


-- created on 2025-11-17
