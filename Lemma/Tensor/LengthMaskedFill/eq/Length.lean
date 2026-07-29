import sympy.matrices.expressions.special
import sympy.tensor.Basic


@[main]
private lemma main
  [Zero α]
-- given
  (X : Tensor α s)
  (d : ℤ)
  (cmp : ℤ → ℤ → Bool) :
-- imply
  (X.masked_fill d cmp).length = X.length := by
-- proof
  unfold Tensor.length Tensor.masked_fill
  split_ifs
  repeat grind


-- created on 2026-07-29
