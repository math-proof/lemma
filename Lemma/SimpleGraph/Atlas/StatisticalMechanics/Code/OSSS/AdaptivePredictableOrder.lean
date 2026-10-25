import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.AdaptivePredictableOrder
open StatMech StatMech.OSSS StatMech.OSSS.AdaptiveCausalKernel


/--
[realizedList_take_succ_eq_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptivePredictableOrder.lean)
-/
@[path]
private lemma realizedList_take_succ_eq_of_agree_eq
  [Fintype E]
  [DecidableEq E]
  {R : Finset E}
  {S : CausalOrder R}
  {x y : ConfigSpace E}
  {t : ℕ}
-- given
  (ht : t < R.card)
  (hxy : Agree ((realizedList S x).take t).toFinset x y) :
-- imply
  (realizedList S y).take (t + 1) = (realizedList S x).take (t + 1) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.realizedList_take_succ_eq_of_agree S x y t ht hxy

/--
[realizedEquiv_predictable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptivePredictableOrder.lean)
-/
@[path]
private lemma realizedEquiv_predictable_eq
  [Fintype E]
  [DecidableEq E]
  {S : CausalOrder (Finset.univ : Finset E)} :
-- imply
  AdaptiveCodingLaw.PredictableOrder (fun x => realizedEquiv S x) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.realizedEquiv_predictable S

/--
[extendDecisionTree_univ_known_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptivePredictableOrder.lean)
-/
@[path]
private lemma extendDecisionTree_univ_known_congr_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {known known' : ConfigSpace E} :
-- imply
  extendDecisionTree T known (Finset.univ : Finset E) = extendDecisionTree T known' Finset.univ := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.extendDecisionTree_univ_known_congr T known known'

/--
[decisionTree_realizedEquiv_predictable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptivePredictableOrder.lean)
-/
@[path]
private lemma decisionTree_realizedEquiv_predictable_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E} :
-- imply
  AdaptiveCodingLaw.PredictableOrder (fun x => realizedEquiv (extendDecisionTree T x (Finset.univ : Finset E)) x) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.decisionTree_realizedEquiv_predictable T

/--
[sharedEdges_extendDecisionTreeAt_eq_sdiff_take](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptivePredictableOrder.lean)
-/
@[path]
private lemma sharedEdges_extendDecisionTreeAt_eq_sdiff_take_eq
  [Fintype E]
  [DecidableEq E]
  {t : ℕ}
  {T : DecisionTree E}
  {known base : ConfigSpace E}
  {R : Finset E}
-- given
  (hknown : ∀ z, z ∉ R → known z = base z) :
-- imply
  sharedEdges (extendDecisionTreeAt t T known R) base = (T.queried base ∩ R) \ ((realizedList (extendDecisionTree T known R) base).take t).toFinset := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sharedEdges_extendDecisionTreeAt_eq_sdiff_take t T known base R hknown

/--
[prefixSet_realizedEquiv_eq_take](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptivePredictableOrder.lean)
-/
@[path]
private lemma prefixSet_realizedEquiv_eq_take_eq
  [Fintype E]
  [DecidableEq E]
  {S : CausalOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E}
  {m : ℕ}
-- given
  (hm : m ≤ Fintype.card E) :
-- imply
  prefixSet (realizedEquiv S base : Fin (Fintype.card E) → E) m = ((realizedList S base).take m).toFinset := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.prefixSet_realizedEquiv_eq_take S base m hm

/--
[realizedList_take_queried_extendDecisionTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptivePredictableOrder.lean)
-/
@[path]
private lemma realizedList_take_queried_extendDecisionTree_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {known base : ConfigSpace E}
  {R : Finset E}
-- given
  (hknown : ∀ z, z ∉ R → known z = base z) :
-- imply
  ((realizedList (extendDecisionTree T known R) base).take ((T.queried base ∩ R).card)).toFinset = T.queried base ∩ R := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.realizedList_take_queried_extendDecisionTree T known base R hknown

/--
[prefixSet_decisionTree_realizedEquiv_queried](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptivePredictableOrder.lean)
-/
@[path]
private lemma prefixSet_decisionTree_realizedEquiv_queried_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {base : ConfigSpace E} :
-- imply
  prefixSet (realizedEquiv (extendDecisionTree T base (Finset.univ : Finset E)) base : Fin (Fintype.card E) → E) (T.queried base).card = T.queried base := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.prefixSet_decisionTree_realizedEquiv_queried T base

/--
[stopVal_decisionTree_realizedEquiv_le_queried_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptivePredictableOrder.lean)
-/
@[path]
private lemma stopVal_decisionTree_realizedEquiv_le_queried_card_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {base : ConfigSpace E}
  {U : Fin (Fintype.card E) → ℝ}
-- given
  (hU : codeMap mu (realizedEquiv (extendDecisionTree T base (Finset.univ : Finset E)) base : Fin (Fintype.card E) → E) U = base) :
-- imply
  AdaptMConditional.stopVal mu (realizedEquiv (extendDecisionTree T base (Finset.univ : Finset E)) base) T.evalR U ≤ (T.queried base).card := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.stopVal_decisionTree_realizedEquiv_le_queried_card mu T base U hU


-- created on 2026-10-23
