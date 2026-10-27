import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Foundations.WeightedFiniteInjection
open Finset Set StatMech


/--
[Fintype.sum_le_mul_sum_of_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/WeightedFiniteInjection.lean)
-/
@[path]
private lemma sum_le_mul_sum_of_injective_eq
  [Fintype Alpha]
  [Fintype Beta]
  {C : Real}
-- given
  (D : Alpha -> Beta)
  (hinj : Function.Injective D)
  (sourceWeight : Alpha -> Real)
  (targetWeight : Beta -> Real)
  (hC : 0 <= C)
  (htarget : forall b, 0 <= targetWeight b)
  (hpoint : forall a, sourceWeight a <= C * targetWeight (D a)) :
-- imply
  (∑ a, sourceWeight a) <= C * ∑ b, targetWeight b := by
-- proof
  apply StatMech.Fintype.sum_le_mul_sum_of_injective D hinj sourceWeight targetWeight C hC htarget hpoint


-- created on 2026-10-23
