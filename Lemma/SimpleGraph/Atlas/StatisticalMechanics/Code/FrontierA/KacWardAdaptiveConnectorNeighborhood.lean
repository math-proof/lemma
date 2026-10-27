import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveConnectorNeighborhood
open StatMech StatMech.FrontierA


/--
[kwHVConnectorCorner_eq_parts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveConnectorNeighborhood.lean)
-/
@[path]
private lemma kwHVConnectorCorner_eq_parts_eq
  {a b : ℂ} :
-- imply
  kwHVConnectorCorner a b = kwHorizontalPart b + kwVerticalPart a := by
-- proof
  apply StatMech.FrontierA.kwHVConnectorCorner_eq_parts a b

/--
[kwVHConnectorCorner_eq_parts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveConnectorNeighborhood.lean)
-/
@[path]
private lemma kwVHConnectorCorner_eq_parts_eq
  {a b : ℂ} :
-- imply
  kwVHConnectorCorner a b = kwHorizontalPart a + kwVerticalPart b := by
-- proof
  apply StatMech.FrontierA.kwVHConnectorCorner_eq_parts a b

/--
[KWAdaptiveConnectorData.corner_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveConnectorNeighborhood.lean)
-/
@[path]
private lemma corner_norm_le_eq
  {a b : ℂ}
  {connector : KWAdaptiveConnectorData a b} :
-- imply
  ‖connector.corner‖ ≤ ‖a‖ + ‖b‖ := by
-- proof
  apply StatMech.FrontierA.KWAdaptiveConnectorData.corner_norm_le connector

/--
[KWAdaptiveConnectorData.corner_mem_ball](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveConnectorNeighborhood.lean)
-/
@[path]
private lemma corner_mem_ball_eq
  {a b : ℂ}
  {connector : KWAdaptiveConnectorData a b}
  {r : ℝ}
-- given
  (ha : ‖a‖ < r / 2)
  (hb : ‖b‖ < r / 2) :
-- imply
  connector.corner ∈ Metric.ball (0 : ℂ) r := by
-- proof
  apply StatMech.FrontierA.KWAdaptiveConnectorData.corner_mem_ball connector ha hb

/--
[KWAdaptiveConnectorData.translated_closedLegs_subset_ball](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveConnectorNeighborhood.lean)
-/
@[path]
private lemma translated_closedLegs_subset_ball_eq
  {a b : ℂ}
  {connector : KWAdaptiveConnectorData a b}
  {v : ℂ}
  {r : ℝ}
-- given
  (hr : 0 < r)
  (ha : ‖a‖ < r / 2)
  (hb : ‖b‖ < r / 2) :
-- imply
  segment ℝ (v + a) (v + connector.corner) ⊆ Metric.ball v r ∧ segment ℝ (v + connector.corner) (v + b) ⊆ Metric.ball v r := by
-- proof
  apply StatMech.FrontierA.KWAdaptiveConnectorData.translated_closedLegs_subset_ball connector v hr ha hb


-- created on 2026-10-23
