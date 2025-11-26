import Lemma.List.Rotate.eq.AppendDrop__Take.of.GeLength
import Lemma.List.GetAppend.eq.Get.of.Lt_Length
import Lemma.List.GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength
open List


@[main]
private lemma main
  {s : List α}
  {d : ℕ}
-- given
  (h_i : i < s.length)
  (h_d : d ≤ s.length) :
-- imply
  have : i < (s.rotate d).length := by simp_all
  (s.rotate d)[i] =
    if h : i < s.length - d then
      have : i < (s.drop d).length := by simp_all
      (s.drop d)[i]
    else
      have : i - (s.length - d) < (s.take d).length := by grind
      (s.take d)[i - (s.length - d)] := by
-- proof
  intro h_i'
  simp [Rotate.eq.AppendDrop__Take.of.GeLength h_d]
  split_ifs with h
  · 
    rw [GetAppend.eq.Get.of.Lt_Length (by simpa)]
    simp
  · 
    rw [GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength]
    · 
      simp
    · 
      simpa using h


-- created on 2025-10-17
