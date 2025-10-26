import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.Tensor.SEqPermuteHeadPermuteTail.of.GtLength_1
import Lemma.Tensor.SEqPermuteHeadS.of.SEq.Eq
import Lemma.Tensor.SEqPermuteHead_1
import Lemma.Tensor.SEqPermuteTailS.of.SEq.Eq
import Lemma.Tensor.SEqPermuteTail_1
open List Tensor


@[main]
private lemma main
-- given
  (h : s ≠ [])
  (X : Tensor α s) :
-- imply
  (X.permuteTail s.length).permuteHead s.length ≃ X := by
-- proof
  by_cases h_s : s.length = 1
  ·
    have h_tail := SEqPermuteTail_1 X
    apply SEq.symm ∘ SEq.trans h_tail.symm
    have h_head := SEqPermuteHead_1 (X.permuteTail 1)
    apply SEq.trans h_head.symm
    apply SEqPermuteHeadS.of.SEq.Eq
    ·
      aesop
    ·
      apply SEqPermuteTailS.of.SEq.Eq
      ·
        aesop
      ·
        rfl
  ·
    have h := GeLength_1.of.Ne_Nil h
    apply SEqPermuteHeadPermuteTail.of.GtLength_1
    omega


-- created on 2025-10-26
