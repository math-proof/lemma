import sympy.tensor.tensor
import Lemma.Basic


@[main]
private lemma main
  [Add α] [Zero α] [Div α] [NatCast α]
-- given
  (X : Tensor α s)
  (n : Tensor α []) :
-- imply
  (X / n).mean = X.mean / n := by
-- proof
  simp [Tensor.mean]
  by_cases h : 0 < s.length
  <;> simp [h]
  · 
    sorry
  · 
    sorry


-- created on 2025-08-29
-- updated on 2025-09-21
