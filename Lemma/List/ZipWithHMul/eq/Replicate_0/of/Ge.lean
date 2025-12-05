import Lemma.List.ZipWith.eq.ZipWith_Take.of.Ge
import Lemma.List.EqLengthTake.of.Ge
import Lemma.List.EqLengthReplicate
import Lemma.List.ZipWithHMul.eq.Replicate_0.of.EqLength
open List


@[main]
private lemma main
  [MulZeroClass α]
  {a : List α}
-- given
  (h : a.length ≥ l) :
-- imply
  List.zipWith HMul.hMul a (List.replicate l 0) = List.replicate l 0 := by
-- proof
  have h_Eq := EqLengthReplicate (0 : α) l
  rw [← h_Eq] at h
  have h₁ := ZipWith.eq.ZipWith_Take.of.Ge h HMul.hMul
  rw [h_Eq] at h₁
  have h_Eq' := EqLengthTake.of.Ge h
  rw [h_Eq] at h_Eq'
  rwa [ZipWithHMul.eq.Replicate_0.of.EqLength h_Eq'] at h₁


-- created on 2025-05-02
