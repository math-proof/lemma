import sympy.tensor.Basic
import sympy.Basic


@[main]
private lemma main
  [Div α]
-- given
  (h : s = s')
  (X Y : Tensor α s) :
-- imply
  have h : Tensor α s = Tensor α s' := by rw [h]
  cast h (X / Y) = cast h X / cast h Y := by
-- proof
  aesop


@[main]
private lemma scalar
  [Div α]
-- given
  (h : s = s')
  (X : Tensor α s)
  (n : Tensor α []) :
-- imply
  have h : Tensor α s = Tensor α s' := by rw [h]
  cast h (X / n) = cast h X / n := by
-- proof
  aesop


-- created on 2025-09-21
