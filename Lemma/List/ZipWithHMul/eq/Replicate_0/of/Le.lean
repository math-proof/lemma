import Lemma.List.EqLengthTake.of.Ge
import Lemma.List.EqLengthReplicate
import Lemma.List.ZipWithHMul.eq.Replicate_0.of.Eq_Length
import Lemma.List.ZipWith.eq.ZipWith__Take.of.Le
open List


@[main]
private lemma main
  [MulZeroClass α]
  {a : List α}
-- given
  (h : a.length ≥ l) :
-- imply
  List.zipWith HMul.hMul (List.replicate l 0) a = List.replicate l 0 := by
-- proof
  have h_Eq := EqLengthReplicate (0 : α) l
  rw [← h_Eq] at h
  have h₁ := ZipWith.eq.ZipWith__Take.of.Le (f := HMul.hMul) h
  rw [h_Eq] at h₁
  have h_Eq' := EqLengthTake.of.Ge h
  rw [h_Eq] at h_Eq'
  have h₂ := ZipWithHMul.eq.Replicate_0.of.Eq_Length h_Eq'.symm
  rwa [h₂] at h₁


-- created on 2025-05-02
