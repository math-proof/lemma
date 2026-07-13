import sympy.Basic
import sympy.tensor.tensor
open Tensor


@[main, fin]
private lemma main
  [Decidable c]
  {i : ℕ}
-- given
  (h : c)
  (t : c → Tensor α s)
  (e : ¬c → Tensor α s)
  (h_i : i < (dite c t e).length) :
-- imply
  (dite c t e)[i] = (t h)[i]'(by grind) := by
-- proof
  aesop


-- created on 2026-07-13
