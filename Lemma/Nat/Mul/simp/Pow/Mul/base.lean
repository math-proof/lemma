import Mathlib.Basic.Real.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℝ}
  {n : ℕ} :
-- imply
  (x * y) ^ n = x ^ n * y ^ n :=
-- proof
  mul_pow x y n


-- created on 2022-07-07
