import Mathlib
import sympy.Basic
import sympy.atlas.Algebra.Polynomial.RootBound
open Polynomial


/--
[aeval_lt_l1Norm_of_monic_of_aeval_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/RootBound.lean)
-/
@[path]
private lemma aeval_lt_l1Norm_of_monic_of_aeval_eq_zero_eq
  [Field K] [Field L] [Algebra K L]
  {v : AbsoluteValue K ℝ}
  {w : AbsoluteValue L ℝ} [AbsoluteValue.LiesOver w v]
  {f : Polynomial K}
  {α : L}
-- given
  (hf : f.Monic)
  (hroot : aeval α f = 0) :
-- imply
  w α < l1Norm v f := by
-- proof
  apply Polynomial.aeval_lt_l1Norm_of_monic_of_aeval_eq_zero v w hf hroot


-- created on 2026-10-20
