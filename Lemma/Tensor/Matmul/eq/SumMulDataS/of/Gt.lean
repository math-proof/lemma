import Lemma.Bool.HEq.of.SEq
import Lemma.Tensor.SEqResize_0.of.Eq_Get_0.GtLength_0
open Bool Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h : n > n')
  (X : Tensor α [n])
  (Y : Tensor α [n']) :
-- imply
  X.einsum Y = (X * (cast (by simp) (Y.resize ⟨0, by simp⟩ n) : Tensor α [n])).sum := by
-- proof
  unfold Tensor.einsum
  split_ifs with h h h h h
  ·
    grind
  ·
    grind
  ·
    simp
    congr
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
      repeat grind
    ·
      grind
  ·
    grind
  ·
    grind
  ·
    grind


-- created on 2026-01-05
-- updated on 2026-07-10
