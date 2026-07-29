import sympy.matrices.expressions.special
import sympy.tensor.Basic


@[main]
private lemma main
  [Zero α]
-- given
  (h : s.length < 2)
  (X : Tensor α s)
  (d : ℤ)
  (cmp : ℤ → ℤ → Bool) :
-- imply
  X.masked_fill d cmp = X := by
-- proof
  unfold Tensor.masked_fill
  simp
  split_ifs
  repeat grind


-- created on 2026-07-29
