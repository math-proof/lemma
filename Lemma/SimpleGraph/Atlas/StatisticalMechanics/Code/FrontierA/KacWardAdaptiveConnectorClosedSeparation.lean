import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveConnectorClosedSeparation
open StatMech StatMech.FrontierA


/--
[KWAdaptiveConnectorData.closedPath_disjoint_rayTails](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveConnectorClosedSeparation.lean)
-/
@[path]
private lemma closedPath_disjoint_rayTails_eq
  {a b : ℂ}
  {connector : KWAdaptiveConnectorData a b}
-- given
  (haRe : a.re ≠ 0)
  (haIm : a.im ≠ 0)
  (hbRe : b.re ≠ 0)
  (hbIm : b.im ≠ 0)
  (hcross : kwComplexCross a b ≠ 0) :
-- imply
  Disjoint (kwConnectorClosedPath a connector.corner b) (kwOpenRayTail a ∪ kwOpenRayTail b) := by
-- proof
  apply StatMech.FrontierA.KWAdaptiveConnectorData.closedPath_disjoint_rayTails connector haRe haIm hbRe hbIm hcross

/--
[KWAdaptiveConnectorData.right_not_mem_firstClosedLeg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveConnectorClosedSeparation.lean)
-/
@[path]
private lemma right_not_mem_firstClosedLeg_eq
  {a b : ℂ}
  {connector : KWAdaptiveConnectorData a b} :
-- imply
  b ∉ segment ℝ a connector.corner := by
-- proof
  apply StatMech.FrontierA.KWAdaptiveConnectorData.right_not_mem_firstClosedLeg connector

/--
[KWAdaptiveConnectorData.left_not_mem_secondClosedLeg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveConnectorClosedSeparation.lean)
-/
@[path]
private lemma left_not_mem_secondClosedLeg_eq
  {a b : ℂ}
  {connector : KWAdaptiveConnectorData a b} :
-- imply
  a ∉ segment ℝ connector.corner b := by
-- proof
  apply StatMech.FrontierA.KWAdaptiveConnectorData.left_not_mem_secondClosedLeg connector

/--
[KWAdaptiveConnectorData.firstClosedLeg_disjoint_rightPortRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveConnectorClosedSeparation.lean)
-/
@[path]
private lemma firstClosedLeg_disjoint_rightPortRay_eq
  {a b : ℂ}
  {connector : KWAdaptiveConnectorData a b}
-- given
  (haRe : a.re ≠ 0)
  (haIm : a.im ≠ 0)
  (hbRe : b.re ≠ 0)
  (hbIm : b.im ≠ 0)
  (hcross : kwComplexCross a b ≠ 0) :
-- imply
  Disjoint (segment ℝ a connector.corner) ({b} ∪ kwOpenRayTail b) := by
-- proof
  apply StatMech.FrontierA.KWAdaptiveConnectorData.firstClosedLeg_disjoint_rightPortRay connector haRe haIm hbRe hbIm hcross

/--
[KWAdaptiveConnectorData.secondClosedLeg_disjoint_leftPortRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveConnectorClosedSeparation.lean)
-/
@[path]
private lemma secondClosedLeg_disjoint_leftPortRay_eq
  {a b : ℂ}
  {connector : KWAdaptiveConnectorData a b}
-- given
  (haRe : a.re ≠ 0)
  (haIm : a.im ≠ 0)
  (hbRe : b.re ≠ 0)
  (hbIm : b.im ≠ 0)
  (hcross : kwComplexCross a b ≠ 0) :
-- imply
  Disjoint (segment ℝ connector.corner b) ({a} ∪ kwOpenRayTail a) := by
-- proof
  apply StatMech.FrontierA.KWAdaptiveConnectorData.secondClosedLeg_disjoint_leftPortRay connector haRe haIm hbRe hbIm hcross


-- created on 2026-10-23
