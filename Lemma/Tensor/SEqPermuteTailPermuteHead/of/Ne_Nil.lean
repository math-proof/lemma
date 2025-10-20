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
    match s with
    | [] =>
      contradiction
    | [n] =>
      simp
      have h_head := SEqPermuteHead_1 X
      apply SEq.symm ∘ SEq.trans h_head.symm
      let X' : Tensor α [n] := cast (by simp) (X.permuteHead 1)
      have h_sim_X' : X' ≃ X := by
        simp [X']
        apply SEqCast.of.SEq.Eq.Eq
        ·
          simp
        ·
          rfl
        ·
          assumption
      have h_tail := SEqPermuteTail_1 X'
      simp [X'] at h_tail
      have h_tail := SEq.of.SEq_Cast h_tail (h := by simp)
      apply SEq.trans h_tail.symm
      rw [PermuteTailCast.eq.Cast_PermuteTail.of.Eq (by simp)]
      apply SEqCast.of.SEq.Eq.Eq
      .
        simp
      .
        simp
      .
        rfl
  ·
    have h := GeLength_1.of.Ne_Nil h
    apply SEqPermuteTailPermuteHead.of.GtLength_1
    omega


-- created on 2025-10-20
