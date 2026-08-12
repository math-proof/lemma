import sympy.Basic
import sympy.tensor.Basic


@[main]
private lemma main
  [Div α]
-- given
  (h : s = s')
  (X Y : Tensor α s) :
-- imply
  have h := congrArg (Tensor α) h
  cast h (X / Y) = cast h X / cast h Y := by
-- proof
  aesop


-- created on 2026-08-12
