/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/RootBound.lean -/

-- Author: @toskua, Avocado

import Mathlib.Algebra.Polynomial.Monic
import Theorem.Algebra.Polynomial.RootBound
import Lemma.Polynomial.RootBound
import Instance.MathlibExtTest.Algebra.Polynomial.RootBound


namespace Polynomial

/-- Zero is a root of `X`, and the root bound holds. -/
example : (AbsoluteValue.abs : AbsoluteValue ℝ ℝ) (0 : ℝ)
    < l1Norm (AbsoluteValue.abs : AbsoluteValue ℝ ℝ) (X : Polynomial ℝ) :=
  aeval_lt_l1Norm_of_monic_of_aeval_eq_zero _ _ monic_X (by simp)

/-- A nonzero root of a monic linear polynomial satisfies the root bound. -/
example : (AbsoluteValue.abs : AbsoluteValue ℝ ℝ) (2 : ℝ)
    < l1Norm (AbsoluteValue.abs : AbsoluteValue ℝ ℝ)
      ((X : Polynomial ℝ) - C 2) :=
  aeval_lt_l1Norm_of_monic_of_aeval_eq_zero _ _ (monic_X_sub_C 2) (by
    rw [aeval_sub, aeval_X, aeval_C]
    exact sub_self 2)

/-- The root bound applies over any field extension through the `LiesOver`
compatibility class. -/
example {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ)
    [AbsoluteValue.LiesOver w v] (f : Polynomial K) (hf : f.Monic)
    (α : L) (hroot : aeval α f = 0) : w α < l1Norm v f :=
  aeval_lt_l1Norm_of_monic_of_aeval_eq_zero v w hf hroot

end Polynomial
