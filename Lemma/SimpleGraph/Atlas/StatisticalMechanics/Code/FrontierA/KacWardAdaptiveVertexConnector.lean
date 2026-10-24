import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveVertexConnector
open StatMech StatMech.FrontierA


/--
[kwHVConnectorCorner_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveVertexConnector.lean)
-/
@[path]
private lemma kwHVConnectorCorner_re_eq
  {a b : ℂ} :
-- imply
  (kwHVConnectorCorner a b).re = b.re := by
-- proof
  apply StatMech.FrontierA.kwHVConnectorCorner_re a b

/--
[kwHVConnectorCorner_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveVertexConnector.lean)
-/
@[path]
private lemma kwHVConnectorCorner_im_eq
  {a b : ℂ} :
-- imply
  (kwHVConnectorCorner a b).im = a.im := by
-- proof
  apply StatMech.FrontierA.kwHVConnectorCorner_im a b

/--
[kwVHConnectorCorner_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveVertexConnector.lean)
-/
@[path]
private lemma kwVHConnectorCorner_re_eq
  {a b : ℂ} :
-- imply
  (kwVHConnectorCorner a b).re = a.re := by
-- proof
  apply StatMech.FrontierA.kwVHConnectorCorner_re a b

/--
[kwVHConnectorCorner_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveVertexConnector.lean)
-/
@[path]
private lemma kwVHConnectorCorner_im_eq
  {a b : ℂ} :
-- imply
  (kwVHConnectorCorner a b).im = b.im := by
-- proof
  apply StatMech.FrontierA.kwVHConnectorCorner_im a b

/--
[kwHVConnector_first_disjoint_leftRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveVertexConnector.lean)
-/
@[path]
private lemma kwHVConnector_first_disjoint_leftRay_eq
  {a b : ℂ}
-- given
  (haIm : a.im ≠ 0) :
-- imply
  Disjoint {z : ℂ | Sbtw ℝ a z (kwHVConnectorCorner a b)} (kwOpenRayTail a) := by
-- proof
  apply StatMech.FrontierA.kwHVConnector_first_disjoint_leftRay a b haIm

/--
[kwHVConnector_second_disjoint_rightRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveVertexConnector.lean)
-/
@[path]
private lemma kwHVConnector_second_disjoint_rightRay_eq
  {a b : ℂ}
-- given
  (hbRe : b.re ≠ 0) :
-- imply
  Disjoint {z : ℂ | Sbtw ℝ (kwHVConnectorCorner a b) z b} (kwOpenRayTail b) := by
-- proof
  apply StatMech.FrontierA.kwHVConnector_second_disjoint_rightRay a b hbRe

/--
[kwVHConnector_first_disjoint_leftRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveVertexConnector.lean)
-/
@[path]
private lemma kwVHConnector_first_disjoint_leftRay_eq
  {a b : ℂ}
-- given
  (haRe : a.re ≠ 0) :
-- imply
  Disjoint {z : ℂ | Sbtw ℝ a z (kwVHConnectorCorner a b)} (kwOpenRayTail a) := by
-- proof
  apply StatMech.FrontierA.kwVHConnector_first_disjoint_leftRay a b haRe

/--
[kwVHConnector_second_disjoint_rightRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveVertexConnector.lean)
-/
@[path]
private lemma kwVHConnector_second_disjoint_rightRay_eq
  {a b : ℂ}
-- given
  (hbIm : b.im ≠ 0) :
-- imply
  Disjoint {z : ℂ | Sbtw ℝ (kwVHConnectorCorner a b) z b} (kwOpenRayTail b) := by
-- proof
  apply StatMech.FrontierA.kwVHConnector_second_disjoint_rightRay a b hbIm

/--
[exists_adaptiveConnector_oppositeRay_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveVertexConnector.lean)
-/
@[path]
private lemma exists_adaptiveConnector_oppositeRay_disjoint_eq
  {a b : ℂ}
-- given
  (haRe : a.re ≠ 0)
  (haIm : a.im ≠ 0)
  (hbRe : b.re ≠ 0)
  (hbIm : b.im ≠ 0) :
-- imply
  (Disjoint {z : ℂ | Sbtw ℝ a z (kwHVConnectorCorner a b)} (kwOpenRayTail b) ∧ Disjoint {z : ℂ | Sbtw ℝ (kwHVConnectorCorner a b) z b} (kwOpenRayTail a)) ∨ (Disjoint {z : ℂ | Sbtw ℝ a z (kwVHConnectorCorner a b)} (kwOpenRayTail b) ∧ Disjoint {z : ℂ | Sbtw ℝ (kwVHConnectorCorner a b) z b} (kwOpenRayTail a)) := by
-- proof
  apply StatMech.FrontierA.exists_adaptiveConnector_oppositeRay_disjoint a b haRe haIm hbRe hbIm

/--
[exists_adaptiveConnectorData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveVertexConnector.lean)
-/
@[path]
private lemma exists_adaptiveConnectorData_eq
  {a b : ℂ}
-- given
  (haRe : a.re ≠ 0)
  (haIm : a.im ≠ 0)
  (hbRe : b.re ≠ 0)
  (hbIm : b.im ≠ 0)
  (hre : a.re ≠ b.re)
  (him : a.im ≠ b.im) :
-- imply
  Nonempty (KWAdaptiveConnectorData a b) := by
-- proof
  apply StatMech.FrontierA.exists_adaptiveConnectorData a b haRe haIm hbRe hbIm hre him

/--
[exists_bounded_incomingScale_both_extents_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveVertexConnector.lean)
-/
@[path]
private lemma exists_bounded_incomingScale_both_extents_lt_eq
  {a b : ℂ}
  {beta cap : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcap : 0 < cap)
  (haRe : a.re ≠ 0)
  (haIm : a.im ≠ 0)
  (hbRe : b.re ≠ 0)
  (hbIm : b.im ≠ 0) :
-- imply
  ∃ alpha : ℝ, 0 < alpha ∧ alpha < cap ∧ := by
-- proof
  apply StatMech.FrontierA.exists_bounded_incomingScale_both_extents_lt a b beta cap hbeta hcap haRe haIm hbRe hbIm

/--
[KWFiniteSimplePolygon.exists_adaptiveConnectorScales](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveVertexConnector.lean)
-/
@[path]
private lemma exists_adaptiveConnectorScales_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {beta cap : ℝ}
-- given
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
  (hbeta : 0 < beta)
  (hcap : 0 < cap) :
-- imply
  ∃ alpha : Fin n → ℝ, (∀ i : Fin n, 0 < alpha i ∧ alpha i < cap ∧ |alpha i * (-polygon.edgeVector (i - 1)).re| < |beta * (polygon.edgeVector i).re| ∧ |alpha i * (-polygon.edgeVector (i - 1)).im| < |beta * (polygon.edgeVector i).im|) ∧ ∀ i : Fin n, Nonempty (KWAdaptiveConnectorData (alpha i * (-polygon.edgeVector (i - 1))) (beta * polygon.edgeVector i)) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_adaptiveConnectorScales polygon hcoords beta cap hbeta hcap


-- created on 2026-10-23
