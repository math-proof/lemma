import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.Order
open NumberField.IsOrder


/--
[le_integralClosure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Order.lean)
-/
@[path]
private lemma le_integralClosure_eq
  [Field K] [NumberField K]
  {O : Subalgebra ℤ K}
-- given
  (h : NumberField.IsOrder K O) :
-- imply
  O ≤ integralClosure ℤ K := by
-- proof
  apply NumberField.IsOrder.le_integralClosure h

/--
[isFractionRing](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Order.lean)
-/
@[path]
private lemma isFractionRing_eq
  [Field K] [NumberField K]
  {O : Subalgebra ℤ K}
-- given
  (h : NumberField.IsOrder K O) :
-- imply
  IsFractionRing O K := by
-- proof
  apply NumberField.IsOrder.isFractionRing h

/--
[exists_div_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Order.lean)
-/
@[path]
private lemma exists_div_eq_eq
  [Field K] [NumberField K]
  {O : Subalgebra ℤ K}
  {x : K}
-- given
  (hO : NumberField.IsOrder K O) :
-- imply
  ∃ (a b : O), b ≠ 0 ∧ (a : K) / (b : K) = x := by
-- proof
  apply NumberField.IsOrder.exists_div_eq hO x

/--
[NumberField.isOrder_integralClosure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Order.lean)
-/
@[path]
private lemma NumberField_isOrder_integralClosure_eq
  [Field K] [NumberField K] :
-- imply
  NumberField.IsOrder K (integralClosure ℤ K) := by
-- proof
  apply NumberField.isOrder_integralClosure K


-- created on 2026-10-20
