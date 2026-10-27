import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamComponentExchangeWeightedCounterexample.Part2
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[weightedCollisionEnds_loopless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeWeightedCounterexample.lean)
-/
@[path]
private lemma weightedCollisionEnds_loopless_eq :
-- imply
  ∀ i ∈ (Finset.univ : Finset (Fin 4)), ¬ (weightedCollisionEnds i).IsDiag := by
-- proof
  apply StatMech.GrahamGHS.FourColor.weightedCollisionEnds_loopless

/--
[weightedCollisionLeftSupports_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeWeightedCounterexample.lean)
-/
@[path]
private lemma weightedCollisionLeftSupports_card_eq :
-- imply
  weightedCollisionLeftSupports.card = 4 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.weightedCollisionLeftSupports_card

/--
[weightedCollisionLeftSupports_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeWeightedCounterexample.lean)
-/
@[path]
private lemma weightedCollisionLeftSupports_left_eq :
-- imply
  ∀ K ∈ weightedCollisionLeftSupports, K ⊆ (Finset.univ : Finset (Fin 4)) ∧ LeftRowSupport weightedCollisionEnds Finset.univ 1 0 2 3 K := by
-- proof
  apply StatMech.GrahamGHS.FourColor.weightedCollisionLeftSupports_left

/--
[weightedCollisionLeftSupports_exchange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeWeightedCounterexample.lean)
-/
@[path]
private lemma weightedCollisionLeftSupports_exchange_eq :
-- imply
  ∀ K ∈ weightedCollisionLeftSupports, exchangeFirstRow weightedCollisionEnds K (Finset.univ \ K) 0 3 = Finset.univ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.weightedCollisionLeftSupports_exchange

/--
[weightedCollisionTarget_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeWeightedCounterexample.lean)
-/
@[path]
private lemma weightedCollisionTarget_right_eq :
-- imply
  RightRowSupport weightedCollisionEnds Finset.univ 1 0 2 3 Finset.univ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.weightedCollisionTarget_right

/--
[weightedCollision_weight_singleton_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeWeightedCounterexample.lean)
-/
@[path]
private lemma weightedCollision_weight_singleton_zero_eq :
-- imply
  rowSupportWeight weightedCollisionEnds Finset.univ {0} = 2 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.weightedCollision_weight_singleton_zero

/--
[weightedCollision_weight_singleton_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeWeightedCounterexample.lean)
-/
@[path]
private lemma weightedCollision_weight_singleton_one_eq :
-- imply
  rowSupportWeight weightedCollisionEnds Finset.univ {1} = 2 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.weightedCollision_weight_singleton_one

/--
[weightedCollision_weight_singleton_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeWeightedCounterexample.lean)
-/
@[path]
private lemma weightedCollision_weight_singleton_two_eq :
-- imply
  rowSupportWeight weightedCollisionEnds Finset.univ {2} = 2 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.weightedCollision_weight_singleton_two

/--
[weightedCollision_weight_parallel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeWeightedCounterexample.lean)
-/
@[path]
private lemma weightedCollision_weight_parallel_eq :
-- imply
  rowSupportWeight weightedCollisionEnds Finset.univ {0, 1, 2} = 4 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.weightedCollision_weight_parallel

/--
[weightedCollision_weight_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeWeightedCounterexample.lean)
-/
@[path]
private lemma weightedCollision_weight_target_eq :
-- imply
  rowSupportWeight weightedCollisionEnds Finset.univ Finset.univ = 4 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.weightedCollision_weight_target

/--
[weightedCollision_source_weight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeWeightedCounterexample.lean)
-/
@[path]
private lemma weightedCollision_source_weight_sum_eq :
-- imply
  (∑ K ∈ weightedCollisionLeftSupports, rowSupportWeight weightedCollisionEnds Finset.univ K) = 10 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.weightedCollision_source_weight_sum

/--
[weightedCollision_fixedTarget_weighted_bound_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeWeightedCounterexample.lean)
-/
@[path]
private lemma weightedCollision_fixedTarget_weighted_bound_false_eq :
-- imply
  ¬ ((∑ K ∈ weightedCollisionLeftSupports, rowSupportWeight weightedCollisionEnds Finset.univ K) ≤ rowSupportWeight weightedCollisionEnds Finset.univ Finset.univ) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.weightedCollision_fixedTarget_weighted_bound_false


-- created on 2026-10-23
