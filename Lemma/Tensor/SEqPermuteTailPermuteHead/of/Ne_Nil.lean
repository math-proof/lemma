import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.Tensor.SEqPermuteTailPermuteHead.of.GtLength_1
import Lemma.Tensor.SEqPermuteTail_1
import Lemma.Tensor.SEqPermuteHead_1
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Tensor.PermuteTailCast.eq.Cast_PermuteTail.of.Eq
open List Tensor Bool


@[main]
private lemma main
-- given
  (h : s ≠ [])
  (X : Tensor α s) :
-- imply
  (X.permuteHead s.length).permuteTail s.length ≃ X := by
-- proof
  by_cases h_s : s.length = 1
  ·
    rw [h_s]
    have h_head := SEqPermuteHead_1 X
    apply SEq.symm ∘ SEq.trans h_head.symm
    have h_tail := SEqPermuteTail_1 (X.permuteHead 1)
    apply SEq.trans h_tail.symm
    rfl
  ·
    have h := GeLength_1.of.Ne_Nil h
    apply SEqPermuteTailPermuteHead.of.GtLength_1
    omega


-- created on 2025-10-20
