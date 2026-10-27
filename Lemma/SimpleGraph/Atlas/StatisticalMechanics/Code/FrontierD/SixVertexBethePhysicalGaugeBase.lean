import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalGaugeBase
open Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexWeightedFiniteDensityGauge_halfFilled_eq_tailDistance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalGaugeBase.lean)
-/
@[path]
private lemma sixVertexWeightedFiniteDensityGauge_halfFilled_eq_tailDistance_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  sixVertexWeightedFiniteDensityGauge hc (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (sixVertexHalfFilledBetheRoots hc k) (sixVertexFourierPhysicalDensityMap hc) = dist (sixVertexSelectedWeightedDensityMap hc k) (sixVertexTailWeightedDensityLimitMap hc htail) := by
-- proof
  apply StatMech.FrontierD.sixVertexWeightedFiniteDensityGauge_halfFilled_eq_tailDistance hc htail k

/--
[sixVertexHalfFilledContinuationGauge_eq_tailDistance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalGaugeBase.lean)
-/
@[path]
private lemma sixVertexHalfFilledContinuationGauge_eq_tailDistance_eq
  {a b c₀ : Real}
  {k : Nat}
-- given
  (ha : 2 < a)
  (hc₀ : c₀ ∈ Set.Icc a b)
  (htail : 2 < sixVertexAnisotropyMagnitude c₀) :
-- imply
  sixVertexContinuationWeightedFiniteDensityGauge ha (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (sixVertexFourierPhysicalDensityFamily ha) (sixVertexHalfFilledBetheContinuationPoint ha hc₀ k) = dist (sixVertexSelectedWeightedDensityMap (ha.trans_le hc₀.1) k) (sixVertexTailWeightedDensityLimitMap (ha.trans_le hc₀.1) htail) := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledContinuationGauge_eq_tailDistance ha hc₀ htail k

/--
[tendsto_sixVertexHalfFilledContinuationGauge_fourierPhysical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalGaugeBase.lean)
-/
@[path]
private lemma tendsto_sixVertexHalfFilledContinuationGauge_fourierPhysical_eq
  {a b c₀ : Real}
-- given
  (ha : 2 < a)
  (hc₀ : c₀ ∈ Set.Icc a b)
  (htail : 2 < sixVertexAnisotropyMagnitude c₀) :
-- imply
  Tendsto (fun k : Nat => sixVertexContinuationWeightedFiniteDensityGauge ha (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (sixVertexFourierPhysicalDensityFamily ha) (sixVertexHalfFilledBetheContinuationPoint ha hc₀ k)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexHalfFilledContinuationGauge_fourierPhysical ha hc₀ htail


-- created on 2026-10-23
