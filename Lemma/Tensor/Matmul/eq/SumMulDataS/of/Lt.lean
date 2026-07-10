import Lemma.Bool.HEq.of.SEq
import Lemma.Nat.EqMax.of.Lt
import Lemma.Tensor.SEqResize_0.of.Eq_Get_0.GtLength_0
open Bool Nat Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_n : n < n')
  (X : Tensor α [n])
  (Y : Tensor α [n']) :
-- imply
  X.einsum Y = (((cast (by simp) (X.resize ⟨0, by simp⟩ n') : Tensor α [n']).data * Y.data).sum : Tensor α []) := by
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
      rw [EqMax.of.Lt h_n]
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
      rw [EqMax.of.Lt h_n]
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


-- created on 2026-01-05
-- updated on 2026-07-10
