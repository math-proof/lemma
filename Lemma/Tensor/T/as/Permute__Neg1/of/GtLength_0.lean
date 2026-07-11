import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.EqPermuteS__Neg.of.Le
import Lemma.List.EqSwap
import Lemma.List.Swap.eq.PermutePermute.of.Lt.GtLength
import Lemma.Tensor.SEqPermute.of.Eq_0
import Lemma.Tensor.SEqPermuteS.of.SEq.Eq.Eq.GtLength
import Lemma.Tensor.SEqPermuteS__Neg.of.Le
open Bool List Tensor


@[main, cast]
private lemma main
-- given
  (h_s : s.length > 0)
  (X : Tensor α s) :
-- imply
  Xᵀ ≃ X.permute ⟨s.length - 1, by grind⟩ (-1) := by
-- proof
  unfold Tensor.T
  unfold Tensor.transpose
  simp
  split_ifs with h h h
  ·
    if h_1 : s.length = 1 then
      apply SEqCast.of.SEq.Eq (by simp [h_1, EqSwap])
      erw [Permute__Neg.eq.Cast.of.Le (i := ⟨s.length - 1, by grind⟩) (by grind)]
      simp
      apply SEq_Cast.of.SEq.Eq
      ·
        simp [h_1]
        erw [EqPermuteS__Neg.of.Le (i := ⟨0, by grind⟩) (by grind)]
        simp
      ·
        symm
        apply SEqPermute.of.Eq_0
        simp [h_1]
    else
      grind
  ·
    grind
  ·
    grind
  ·
    if h_1 : s.length ≥ 2 then
      apply SEqCast.of.SEq.Eq
      ·
        rw [Swap.eq.PermutePermute.of.Lt.GtLength (by grind) (by grind)]
        congr 1
        ·
          simp
          grind
        ·
          simp
          grind
        ·
          simp
          grind
      ·
        apply SEqPermuteS.of.SEq.Eq.Eq.GtLength
        ·
          simp
          grind
        ·
          simp
          grind
        ·
          apply SEqPermute.of.Eq_0
          simp
          grind
    else
      grind


-- created on 2026-07-11
