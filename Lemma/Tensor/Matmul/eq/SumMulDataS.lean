import Lemma.Bool.HEq.of.SEq
import Lemma.Tensor.SEqResize_0.of.Eq_Get_0.GtLength_0
open Bool Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X Y : Tensor α [n]) :
-- imply
  X.matmul Y = ((X.data * Y.data).sum : Tensor α []) := by
-- proof
  unfold Tensor.matmul
  split_ifs with h h
  ·
    grind
  ·
    simp
    congr
    ·
      simp
    ·
      grind
    ·
      grind
    ·
      grind
    ·
      grind
    ·
      grind
    ·
      grind
    ·
      apply HEq.of.SEq
      apply SEqResize_0.of.Eq_Get_0.GtLength_0
      ·
        simp
      ·
        grind
    ·
      grind
    ·
      apply HEq.of.SEq
      apply SEqResize_0.of.Eq_Get_0.GtLength_0
      ·
        simp
      ·
        grind
  ·
    grind


-- created on 2026-01-05
-- updated on 2026-07-10
