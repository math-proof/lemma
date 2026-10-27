import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIncidentStairPatch.Part2
open StatMech StatMech.FrontierA


/--
[mul_sub_pos_of_abs_lt_abs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIncidentStairPatch.lean)
-/
@[path]
private lemma mul_sub_pos_of_abs_lt_abs_eq
  {x y : ℝ}
-- given
  (h : |x| < |y|) :
-- imply
  0 < y * (y - x) := by
-- proof
  apply StatMech.FrontierA.mul_sub_pos_of_abs_lt_abs h

/--
[exists_incomingScale_horizontal_extent_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIncidentStairPatch.lean)
-/
@[path]
private lemma exists_incomingScale_horizontal_extent_lt_eq
  {a b : ℂ}
  {beta : ℝ}
-- given
  (hbeta : 0 < beta)
  (haRe : a.re ≠ 0)
  (hbRe : b.re ≠ 0) :
-- imply
  ∃ alpha : ℝ, 0 < alpha ∧ := by
-- proof
  apply StatMech.FrontierA.exists_incomingScale_horizontal_extent_lt a b beta hbeta haRe hbRe

/--
[exists_bounded_incomingScale_horizontal_extent_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIncidentStairPatch.lean)
-/
@[path]
private lemma exists_bounded_incomingScale_horizontal_extent_lt_eq
  {a b : ℂ}
  {beta cap : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcap : 0 < cap)
  (haRe : a.re ≠ 0)
  (hbRe : b.re ≠ 0) :
-- imply
  ∃ alpha : ℝ, 0 < alpha ∧ alpha < cap ∧ := by
-- proof
  apply StatMech.FrontierA.exists_bounded_incomingScale_horizontal_extent_lt a b beta cap hbeta hcap haRe hbRe

/--
[KWFiniteSimplePolygon.exists_incidentPatchScales](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIncidentStairPatch.lean)
-/
@[path]
private lemma exists_incidentPatchScales_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {beta cap : ℝ}
-- given
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
  (hbeta : 0 < beta)
  (hcap : 0 < cap) :
-- imply
  ∃ alpha : Fin n → ℝ, ∀ i : Fin n, 0 < alpha i ∧ alpha i < cap ∧ := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_incidentPatchScales polygon hcoords beta cap hbeta hcap

/--
[kw_incidentPatch_incomingHorizontal_disjoint_outgoingVertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIncidentStairPatch.lean)
-/
@[path]
private lemma kw_incidentPatch_incomingHorizontal_disjoint_outgoingVertical_eq
  {v a b : ℂ}
  {alpha beta : ℝ}
-- given
  (hbeta : 0 < beta)
  (hbIm : b.im ≠ 0)
  (hextent : |alpha * a.re| < |beta * b.re|) :
-- imply
  Disjoint {z : ℂ | Sbtw ℝ (kwIncomingPatchBase v a alpha) z (kwIncomingPatchCorner v a alpha)} {z : ℂ | Sbtw ℝ (kwOutgoingPatchCorner v b beta) z (kwOutgoingPatchEnd v b beta)} := by
-- proof
  apply StatMech.FrontierA.kw_incidentPatch_incomingHorizontal_disjoint_outgoingVertical v a b alpha beta hbeta hbIm hextent

/--
[kw_incidentPatch_incomingHorizontal_disjoint_outgoingHorizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIncidentStairPatch.lean)
-/
@[path]
private lemma kw_incidentPatch_incomingHorizontal_disjoint_outgoingHorizontal_eq
  {v a b : ℂ}
  {alpha beta : ℝ}
-- given
  (halpha : 0 < alpha)
  (haRe : a.re ≠ 0)
  (haIm : a.im ≠ 0) :
-- imply
  Disjoint {z : ℂ | Sbtw ℝ (kwIncomingPatchBase v a alpha) z (kwIncomingPatchCorner v a alpha)} {z : ℂ | Sbtw ℝ v z (kwOutgoingPatchCorner v b beta)} := by
-- proof
  apply StatMech.FrontierA.kw_incidentPatch_incomingHorizontal_disjoint_outgoingHorizontal v a b alpha beta halpha haRe haIm

/--
[kw_incidentPatch_incomingVertical_disjoint_outgoingVertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIncidentStairPatch.lean)
-/
@[path]
private lemma kw_incidentPatch_incomingVertical_disjoint_outgoingVertical_eq
  {v a b : ℂ}
  {alpha beta : ℝ}
-- given
  (halpha : 0 < alpha)
  (hbeta : 0 < beta)
  (haIm : a.im ≠ 0)
  (hbRe : b.re ≠ 0) :
-- imply
  Disjoint {z : ℂ | Sbtw ℝ (kwIncomingPatchCorner v a alpha) z v} {z : ℂ | Sbtw ℝ (kwOutgoingPatchCorner v b beta) z (kwOutgoingPatchEnd v b beta)} := by
-- proof
  apply StatMech.FrontierA.kw_incidentPatch_incomingVertical_disjoint_outgoingVertical v a b alpha beta halpha hbeta haIm hbRe

/--
[kw_incidentPatch_incomingVertical_disjoint_outgoingHorizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIncidentStairPatch.lean)
-/
@[path]
private lemma kw_incidentPatch_incomingVertical_disjoint_outgoingHorizontal_eq
  {v a b : ℂ}
  {alpha beta : ℝ}
-- given
  (halpha : 0 < alpha)
  (hbeta : 0 < beta)
  (haIm : a.im ≠ 0)
  (hbRe : b.re ≠ 0) :
-- imply
  Disjoint {z : ℂ | Sbtw ℝ (kwIncomingPatchCorner v a alpha) z v} {z : ℂ | Sbtw ℝ v z (kwOutgoingPatchCorner v b beta)} := by
-- proof
  apply StatMech.FrontierA.kw_incidentPatch_incomingVertical_disjoint_outgoingHorizontal v a b alpha beta halpha hbeta haIm hbRe

/--
[kw_incidentPatch_incomingHorizontal_closed_disjoint_outgoingVertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIncidentStairPatch.lean)
-/
@[path]
private lemma kw_incidentPatch_incomingHorizontal_closed_disjoint_outgoingVertical_eq
  {v a b : ℂ}
  {alpha beta : ℝ}
-- given
  (hbeta : 0 < beta)
  (hbIm : b.im ≠ 0)
  (hextent : |alpha * a.re| < |beta * b.re|) :
-- imply
  Disjoint (segment ℝ (kwIncomingPatchBase v a alpha) (kwIncomingPatchCorner v a alpha)) (segment ℝ (kwOutgoingPatchCorner v b beta) (kwOutgoingPatchEnd v b beta)) := by
-- proof
  apply StatMech.FrontierA.kw_incidentPatch_incomingHorizontal_closed_disjoint_outgoingVertical v a b alpha beta hbeta hbIm hextent

/--
[kw_incidentPatch_incomingHorizontal_closed_disjoint_outgoingHorizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIncidentStairPatch.lean)
-/
@[path]
private lemma kw_incidentPatch_incomingHorizontal_closed_disjoint_outgoingHorizontal_eq
  {v a b : ℂ}
  {alpha beta : ℝ}
-- given
  (halpha : 0 < alpha)
  (haRe : a.re ≠ 0)
  (haIm : a.im ≠ 0) :
-- imply
  Disjoint (segment ℝ (kwIncomingPatchBase v a alpha) (kwIncomingPatchCorner v a alpha)) (segment ℝ v (kwOutgoingPatchCorner v b beta)) := by
-- proof
  apply StatMech.FrontierA.kw_incidentPatch_incomingHorizontal_closed_disjoint_outgoingHorizontal v a b alpha beta halpha haRe haIm

/--
[kw_incidentPatch_incomingVertical_closed_disjoint_outgoingVertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIncidentStairPatch.lean)
-/
@[path]
private lemma kw_incidentPatch_incomingVertical_closed_disjoint_outgoingVertical_eq
  {v a b : ℂ}
  {alpha beta : ℝ}
-- given
  (halpha : 0 < alpha)
  (hbeta : 0 < beta)
  (haIm : a.im ≠ 0)
  (hbRe : b.re ≠ 0) :
-- imply
  Disjoint (segment ℝ (kwIncomingPatchCorner v a alpha) v) (segment ℝ (kwOutgoingPatchCorner v b beta) (kwOutgoingPatchEnd v b beta)) := by
-- proof
  apply StatMech.FrontierA.kw_incidentPatch_incomingVertical_closed_disjoint_outgoingVertical v a b alpha beta halpha hbeta haIm hbRe

/--
[kw_incidentPatch_pairwise_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIncidentStairPatch.lean)
-/
@[path]
private lemma kw_incidentPatch_pairwise_disjoint_eq
  {v a b : ℂ}
  {alpha beta : ℝ}
-- given
  (halpha : 0 < alpha)
  (hbeta : 0 < beta)
  (haRe : a.re ≠ 0)
  (haIm : a.im ≠ 0)
  (hbRe : b.re ≠ 0)
  (hbIm : b.im ≠ 0)
  (hextent : |alpha * a.re| < |beta * b.re|) :
-- imply
  Disjoint ({z : ℂ | Sbtw ℝ (kwIncomingPatchBase v a alpha) z (kwIncomingPatchCorner v a alpha)} ∪ {z : ℂ | Sbtw ℝ (kwIncomingPatchCorner v a alpha) z v}) ({z : ℂ | Sbtw ℝ v z (kwOutgoingPatchCorner v b beta)} ∪ {z : ℂ | Sbtw ℝ (kwOutgoingPatchCorner v b beta) z (kwOutgoingPatchEnd v b beta)}) := by
-- proof
  apply StatMech.FrontierA.kw_incidentPatch_pairwise_disjoint v a b alpha beta halpha hbeta haRe haIm hbRe hbIm hextent


-- created on 2026-10-23
