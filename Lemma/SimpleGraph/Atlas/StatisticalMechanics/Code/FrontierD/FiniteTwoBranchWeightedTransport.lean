import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FiniteTwoBranchWeightedTransport
open Finset StatMech StatMech.FrontierD


/--
[fintype_sum_comp_le_sum_of_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteTwoBranchWeightedTransport.lean)
-/
@[path]
private lemma fintype_sum_comp_le_sum_of_injective_eq
  [Fintype Source]
  [Fintype Target]
-- given
  (map : Source -> Target)
  (hinjective : Function.Injective map)
  (weight : Target -> Real)
  (hnonneg : forall target, 0 <= weight target) :
-- imply
  (∑ source, weight (map source)) <= ∑ target, weight target := by
-- proof
  apply StatMech.FrontierD.fintype_sum_comp_le_sum_of_injective map hinjective weight hnonneg

/--
[fintype_sum_le_of_twoBranchWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteTwoBranchWeightedTransport.lean)
-/
@[path]
private lemma fintype_sum_le_of_twoBranchWeight_eq
  [Fintype Source]
  [Fintype Target]
-- given
  (branch : Bool -> Source -> Target)
  (hinjective : forall choice, Function.Injective (branch choice))
  (sourceWeight : Source -> Real)
  (targetWeight : Target -> Real)
  (htargetNonneg : forall target, 0 <= targetWeight target)
  (hlocal : forall source, 2 * sourceWeight source <= targetWeight (branch false source) + targetWeight (branch true source)) :
-- imply
  (∑ source, sourceWeight source) <= ∑ target, targetWeight target := by
-- proof
  apply StatMech.FrontierD.fintype_sum_le_of_twoBranchWeight branch hinjective sourceWeight targetWeight htargetNonneg hlocal

/--
[two_mul_le_add_of_sq_le_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteTwoBranchWeightedTransport.lean)
-/
@[path]
private lemma two_mul_le_add_of_sq_le_mul_eq
  {x y z : Real}
-- given
  (hx : 0 <= x)
  (hy : 0 <= y)
  (hz : 0 <= z)
  (hprod : z ^ 2 <= x * y) :
-- imply
  2 * z <= x + y := by
-- proof
  apply StatMech.FrontierD.two_mul_le_add_of_sq_le_mul hx hy hz hprod

/--
[two_mul_pow_le_pow_add_pow_of_twice_le_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteTwoBranchWeightedTransport.lean)
-/
@[path]
private lemma two_mul_pow_le_pow_add_pow_of_twice_le_add_eq
  {c : Real}
  {source first second : Nat}
-- given
  (hc : 1 <= c)
  (hgrade : 2 * source <= first + second) :
-- imply
  2 * c ^ source <= c ^ first + c ^ second := by
-- proof
  apply StatMech.FrontierD.two_mul_pow_le_pow_add_pow_of_twice_le_add hc hgrade


-- created on 2026-10-23
