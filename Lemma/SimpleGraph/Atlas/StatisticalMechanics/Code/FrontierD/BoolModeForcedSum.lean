import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.BoolModeForcedSum
open Finset StatMech StatMech.FrontierD


/--
[forcedBoolModeSum_eq_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/BoolModeForcedSum.lean)
-/
@[path]
private lemma forcedBoolModeSum_eq_product_eq
  [Fintype alpha]
  [DecidableEq alpha]
  {S : Finset alpha}
-- given
  (forced : alpha -> Bool)
  (f : alpha -> Bool -> Real) :
-- imply
  forcedBoolModeSum S forced f = ∏ x : alpha, if x ∈ S then f x (forced x) else f x false + f x true := by
-- proof
  apply StatMech.FrontierD.forcedBoolModeSum_eq_product S forced f

/--
[sum_boolMode_product_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/BoolModeForcedSum.lean)
-/
@[path]
private lemma sum_boolMode_product_eq_eq
  [Fintype alpha]
  [DecidableEq alpha]
-- given
  (f : alpha -> Bool -> Real) :
-- imply
  (∑ mode : alpha -> Bool, ∏ x, f x (mode x)) = ∏ x : alpha, (f x false + f x true) := by
-- proof
  apply StatMech.FrontierD.sum_boolMode_product_eq f

/--
[sum_boolMode_product_le_pow_mul_forced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/BoolModeForcedSum.lean)
-/
@[path]
private lemma sum_boolMode_product_le_pow_mul_forced_eq
  [Fintype alpha]
  [DecidableEq alpha]
  {S : Finset alpha}
  {K : Real}
-- given
  (forced : alpha -> Bool)
  (f : alpha -> Bool -> Real)
  (hf : forall x b, 0 <= f x b)
  (hlocal : forall x, x ∈ S -> f x false + f x true <= K * f x (forced x)) :
-- imply
  (∑ mode : alpha -> Bool, ∏ x, f x (mode x)) <= K ^ S.card * forcedBoolModeSum S forced f := by
-- proof
  apply StatMech.FrontierD.sum_boolMode_product_le_pow_mul_forced S forced f K hf hlocal


-- created on 2026-10-23
