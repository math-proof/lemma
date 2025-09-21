import sympy.tensor.tensor
import Lemma.Basic


@[main]
private lemma main
  [Add α] [Zero α] [Div α] [NatCast α]
-- given
  (X : Tensor α s)
  (n : Tensor α []) :
-- imply
  (X / n).sum = X.sum / n := by
-- proof
  unfold Tensor.sum
  by_cases h : 0 < s.length
  <;> simp [h]
  ·
    sorry
  ·
    simp at h
    aesop


-- created on 2025-09-21
