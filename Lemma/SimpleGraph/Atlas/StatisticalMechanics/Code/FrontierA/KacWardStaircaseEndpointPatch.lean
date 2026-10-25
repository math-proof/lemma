import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStaircaseEndpointPatch
open StatMech StatMech.FrontierA


/--
[kwEndpointParameter_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseEndpointPatch.lean)
-/
@[path]
private lemma kwEndpointParameter_one_eq
  {M : ℕ}
  {beta alpha : ℝ}
-- given
  (hM : 0 < M) :
-- imply
  kwEndpointParameter M beta alpha (1 : Fin (M + 3)) = beta := by
-- proof
  apply StatMech.FrontierA.kwEndpointParameter_one M beta alpha hM

/--
[kwEndpointParameter_penultimate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseEndpointPatch.lean)
-/
@[path]
private lemma kwEndpointParameter_penultimate_eq
  {M : ℕ}
  {beta alpha : ℝ}
-- given
  (hM : 0 < M) :
-- imply
  kwEndpointParameter M beta alpha (Fin.last (M + 1)).castSucc = 1 - alpha := by
-- proof
  apply StatMech.FrontierA.kwEndpointParameter_penultimate M beta alpha hM

/--
[kwEndpointParameter_step_le_max](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseEndpointPatch.lean)
-/
@[path]
private lemma kwEndpointParameter_step_le_max_eq
  {M : ℕ}
  {beta alpha : ℝ}
  {k : Fin (M + 2)}
-- given
  (hM : 0 < M)
  (hbeta : 0 ≤ beta)
  (halpha : 0 ≤ alpha)
  (hsum : alpha + beta < 1) :
-- imply
  kwEndpointParameter M beta alpha k.succ - kwEndpointParameter M beta alpha k.castSucc ≤ max beta (max alpha (M : ℝ)⁻¹) := by
-- proof
  apply StatMech.FrontierA.kwEndpointParameter_step_le_max M beta alpha hM hbeta halpha hsum k

/--
[kwEndpointParameter_middle_step_le_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseEndpointPatch.lean)
-/
@[path]
private lemma kwEndpointParameter_middle_step_le_inv_eq
  {M : ℕ}
  {beta alpha : ℝ}
  {k : Fin (M + 2)}
-- given
  (hM : 0 < M)
  (hbeta : 0 ≤ beta)
  (halpha : 0 ≤ alpha)
  (hk0 : k ≠ 0)
  (hklast : k ≠ Fin.last (M + 1)) :
-- imply
  kwEndpointParameter M beta alpha k.succ - kwEndpointParameter M beta alpha k.castSucc ≤ (M : ℝ)⁻¹ := by
-- proof
  apply StatMech.FrontierA.kwEndpointParameter_middle_step_le_inv M beta alpha hM hbeta halpha k hk0 hklast

/--
[KWStairParameterData.corner_zero_eq_outgoingPatchCorner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseEndpointPatch.lean)
-/
@[path]
private lemma corner_zero_eq_outgoingPatchCorner_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {beta : ℝ}
-- given
  (data : KWStairParameterData (S := S) polygon)
  (hbeta : data.parameter i (0 : Fin S).succ = beta) :
-- imply
  data.corner i 0 = kwOutgoingPatchCorner (polygon.vertex i) (polygon.edgeVector i) beta := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.corner_zero_eq_outgoingPatchCorner data i beta hbeta

/--
[KWStairParameterData.base_one_eq_outgoingPatchEnd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseEndpointPatch.lean)
-/
@[path]
private lemma base_one_eq_outgoingPatchEnd_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {beta : ℝ}
-- given
  (data : KWStairParameterData (S := S) polygon)
  (hbeta : data.parameter i (0 : Fin S).succ = beta) :
-- imply
  data.base i (0 : Fin S).succ = kwOutgoingPatchEnd (polygon.vertex i) (polygon.edgeVector i) beta := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.base_one_eq_outgoingPatchEnd data i beta hbeta

/--
[KWStairParameterData.base_penultimate_eq_incomingPatchBase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseEndpointPatch.lean)
-/
@[path]
private lemma base_penultimate_eq_incomingPatchBase_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {alpha : ℝ}
-- given
  (data : KWStairParameterData (S := M + 1) polygon)
  (halpha : data.parameter i (Fin.last M).castSucc = 1 - alpha) :
-- imply
  data.base i (Fin.last M).castSucc = kwIncomingPatchBase (polygon.vertex (i + 1)) (-polygon.edgeVector i) alpha := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.base_penultimate_eq_incomingPatchBase data i alpha halpha

/--
[KWStairParameterData.corner_last_eq_incomingPatchCorner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseEndpointPatch.lean)
-/
@[path]
private lemma corner_last_eq_incomingPatchCorner_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {alpha : ℝ}
-- given
  (data : KWStairParameterData (S := M + 1) polygon)
  (halpha : data.parameter i (Fin.last M).castSucc = 1 - alpha) :
-- imply
  data.corner i (Fin.last M) = kwIncomingPatchCorner (polygon.vertex (i + 1)) (-polygon.edgeVector i) alpha := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.corner_last_eq_incomingPatchCorner data i alpha halpha

/--
[KWStairParameterData.incident_endpoint_legs_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseEndpointPatch.lean)
-/
@[path]
private lemma incident_endpoint_legs_disjoint_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {alpha beta : ℝ}
-- given
  (data : KWStairParameterData (S := M + 1) polygon)
  (halphaParameter : data.parameter i (Fin.last M).castSucc = 1 - alpha)
  (hbetaParameter : data.parameter (i + 1) (0 : Fin (M + 1)).succ = beta)
  (halpha : 0 < alpha)
  (hbeta : 0 < beta)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
  (hextent : |alpha * (-polygon.edgeVector i).re| < |beta * (polygon.edgeVector (i + 1)).re|) :
-- imply
  Disjoint ({z : ℂ | Sbtw ℝ (data.base i (Fin.last M).castSucc) z (data.corner i (Fin.last M))} ∪ {z : ℂ | Sbtw ℝ (data.corner i (Fin.last M)) z (polygon.vertex (i + 1))}) ({z : ℂ | Sbtw ℝ (polygon.vertex (i + 1)) z (data.corner (i + 1) 0)} ∪ {z : ℂ | Sbtw ℝ (data.corner (i + 1) 0) z (data.base (i + 1) (0 : Fin (M + 1)).succ)}) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.incident_endpoint_legs_disjoint data i alpha beta halphaParameter hbetaParameter halpha hbeta hcoords hextent

/--
[kwEndpointParameterData_parameter_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseEndpointPatch.lean)
-/
@[path]
private lemma kwEndpointParameterData_parameter_one_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {beta : ℝ}
  {alpha : Fin n → ℝ}
  {i : Fin n}
-- given
  (hM : 0 < M)
  (hbeta : 0 < beta)
  (halpha : ∀ i, 0 < alpha i)
  (hsum : ∀ i, alpha i + beta < 1) :
-- imply
  (kwEndpointParameterData polygon M beta alpha hM hbeta halpha hsum).parameter i (0 : Fin (M + 2)).succ = beta := by
-- proof
  apply StatMech.FrontierA.kwEndpointParameterData_parameter_one polygon beta alpha hM hbeta halpha hsum i

/--
[kwEndpointParameterData_parameter_penultimate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseEndpointPatch.lean)
-/
@[path]
private lemma kwEndpointParameterData_parameter_penultimate_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {beta : ℝ}
  {alpha : Fin n → ℝ}
  {i : Fin n}
-- given
  (hM : 0 < M)
  (hbeta : 0 < beta)
  (halpha : ∀ i, 0 < alpha i)
  (hsum : ∀ i, alpha i + beta < 1) :
-- imply
  (kwEndpointParameterData polygon M beta alpha hM hbeta halpha hsum).parameter i (Fin.last (M + 1)).castSucc = 1 - alpha (i + 1) := by
-- proof
  apply StatMech.FrontierA.kwEndpointParameterData_parameter_penultimate polygon beta alpha hM hbeta halpha hsum i

/--
[kwEndpointParameterData_incident_legs_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseEndpointPatch.lean)
-/
@[path]
private lemma kwEndpointParameterData_incident_legs_disjoint_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {beta : ℝ}
  {alpha : Fin n → ℝ}
  {i : Fin n}
-- given
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
  (hM : 0 < M)
  (hbeta : 0 < beta)
  (halpha : ∀ i, 0 < alpha i)
  (hsum : ∀ i, alpha i + beta < 1)
  (hextent : ∀ i : Fin n, |alpha i * (-polygon.edgeVector (i - 1)).re| < |beta * (polygon.edgeVector i).re|) :
-- imply
  let data := kwEndpointParameterData polygon M beta alpha hM hbeta halpha hsum Disjoint ({z : ℂ | Sbtw ℝ (data.base i (Fin.last (M + 1)).castSucc) z (data.corner i (Fin.last (M + 1)))} ∪ {z : ℂ | Sbtw ℝ (data.corner i (Fin.last (M + 1))) z (polygon.vertex (i + 1))}) ({z : ℂ | Sbtw ℝ (polygon.vertex (i + 1)) z (data.corner (i + 1) 0)} ∪ {z : ℂ | Sbtw ℝ (data.corner (i + 1) 0) z (data.base (i + 1) (0 : Fin (M + 2)).succ)}) := by
-- proof
  apply StatMech.FrontierA.kwEndpointParameterData_incident_legs_disjoint polygon hcoords beta alpha hM hbeta halpha hsum hextent i

/--
[kwOutgoingPatchCorner_mem_ball](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseEndpointPatch.lean)
-/
@[path]
private lemma kwOutgoingPatchCorner_mem_ball_eq
  {v b : ℂ}
  {beta R : ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (hsize : beta * ‖b‖ < R) :
-- imply
  kwOutgoingPatchCorner v b beta ∈ Metric.ball v R := by
-- proof
  apply StatMech.FrontierA.kwOutgoingPatchCorner_mem_ball v b beta R hbeta hsize

/--
[kwOutgoingPatchEnd_mem_ball](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseEndpointPatch.lean)
-/
@[path]
private lemma kwOutgoingPatchEnd_mem_ball_eq
  {v b : ℂ}
  {beta R : ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (hsize : beta * ‖b‖ < R) :
-- imply
  kwOutgoingPatchEnd v b beta ∈ Metric.ball v R := by
-- proof
  apply StatMech.FrontierA.kwOutgoingPatchEnd_mem_ball v b beta R hbeta hsize

/--
[kwIncomingPatchBase_mem_ball](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseEndpointPatch.lean)
-/
@[path]
private lemma kwIncomingPatchBase_mem_ball_eq
  {v a : ℂ}
  {alpha R : ℝ}
-- given
  (halpha : 0 ≤ alpha)
  (hsize : alpha * ‖a‖ < R) :
-- imply
  kwIncomingPatchBase v a alpha ∈ Metric.ball v R := by
-- proof
  apply StatMech.FrontierA.kwIncomingPatchBase_mem_ball v a alpha R halpha hsize

/--
[kwIncomingPatchCorner_mem_ball](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseEndpointPatch.lean)
-/
@[path]
private lemma kwIncomingPatchCorner_mem_ball_eq
  {v a : ℂ}
  {alpha R : ℝ}
-- given
  (halpha : 0 ≤ alpha)
  (hsize : alpha * ‖a‖ < R) :
-- imply
  kwIncomingPatchCorner v a alpha ∈ Metric.ball v R := by
-- proof
  apply StatMech.FrontierA.kwIncomingPatchCorner_mem_ball v a alpha R halpha hsize

/--
[KWStairParameterData.incident_endpoint_legs_subset_ball](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseEndpointPatch.lean)
-/
@[path]
private lemma incident_endpoint_legs_subset_ball_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {alpha beta R : ℝ}
-- given
  (data : KWStairParameterData (S := M + 1) polygon)
  (halphaParameter : data.parameter i (Fin.last M).castSucc = 1 - alpha)
  (hbetaParameter : data.parameter (i + 1) (0 : Fin (M + 1)).succ = beta)
  (hR : 0 < R)
  (halpha : 0 ≤ alpha)
  (hbeta : 0 ≤ beta)
  (halphaSize : alpha * ‖polygon.edgeVector i‖ < R)
  (hbetaSize : beta * ‖polygon.edgeVector (i + 1)‖ < R) :
-- imply
  segment ℝ (data.base i (Fin.last M).castSucc) (data.corner i (Fin.last M)) ⊆ Metric.ball (polygon.vertex (i + 1)) R ∧ segment ℝ (data.corner i (Fin.last M)) (polygon.vertex (i + 1)) ⊆ Metric.ball (polygon.vertex (i + 1)) R ∧ segment ℝ (polygon.vertex (i + 1)) (data.corner (i + 1) 0) ⊆ Metric.ball (polygon.vertex (i + 1)) R ∧ segment ℝ (data.corner (i + 1) 0) (data.base (i + 1) (0 : Fin (M + 1)).succ) ⊆ Metric.ball (polygon.vertex (i + 1)) R := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.incident_endpoint_legs_subset_ball data i alpha beta R halphaParameter hbetaParameter hR halpha hbeta halphaSize hbetaSize

/--
[KWStairParameterData.rawClosedEdge_even_eq_segment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseEndpointPatch.lean)
-/
@[path]
private lemma rawClosedEdge_even_eq_segment_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin S}
-- given
  (data : KWStairParameterData (S := S) polygon) :
-- imply
  kwRawClosedEdge data.vertex (kwStairEvenIndex i k) = segment ℝ (data.base i k.castSucc) (data.corner i k) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.rawClosedEdge_even_eq_segment data i k

/--
[KWStairParameterData.rawClosedEdge_odd_last_eq_segment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseEndpointPatch.lean)
-/
@[path]
private lemma rawClosedEdge_odd_last_eq_segment_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (data : KWStairParameterData (S := M + 1) polygon) :
-- imply
  kwRawClosedEdge data.vertex (kwStairOddIndex i (Fin.last M)) = segment ℝ (data.corner i (Fin.last M)) (polygon.vertex (i + 1)) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.rawClosedEdge_odd_last_eq_segment data i

/--
[KWStairParameterData.rawClosedEdge_odd_zero_eq_segment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseEndpointPatch.lean)
-/
@[path]
private lemma rawClosedEdge_odd_zero_eq_segment_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (data : KWStairParameterData (S := M + 2) polygon) :
-- imply
  kwRawClosedEdge data.vertex (kwStairOddIndex i (0 : Fin (M + 2))) = segment ℝ (data.corner i 0) (data.base i (0 : Fin (M + 2)).succ) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.rawClosedEdge_odd_zero_eq_segment data i

/--
[KWStairParameterData.incident_nonconsecutive_rawEdges_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseEndpointPatch.lean)
-/
@[path]
private lemma incident_nonconsecutive_rawEdges_disjoint_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {alpha beta : ℝ}
-- given
  (data : KWStairParameterData (S := M + 2) polygon)
  (halphaParameter : data.parameter i (Fin.last (M + 1)).castSucc = 1 - alpha)
  (hbetaParameter : data.parameter (i + 1) (0 : Fin (M + 2)).succ = beta)
  (halpha : 0 < alpha)
  (hbeta : 0 < beta)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
  (hextent : |alpha * (-polygon.edgeVector i).re| < |beta * (polygon.edgeVector (i + 1)).re|) :
-- imply
  Disjoint (kwRawClosedEdge data.vertex (kwStairEvenIndex i (Fin.last (M + 1)))) (kwRawClosedEdge data.vertex (kwStairEvenIndex (i + 1) 0)) ∧ Disjoint (kwRawClosedEdge data.vertex (kwStairEvenIndex i (Fin.last (M + 1)))) (kwRawClosedEdge data.vertex (kwStairOddIndex (i + 1) 0)) ∧ Disjoint (kwRawClosedEdge data.vertex (kwStairOddIndex i (Fin.last (M + 1)))) (kwRawClosedEdge data.vertex (kwStairOddIndex (i + 1) 0)) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.incident_nonconsecutive_rawEdges_disjoint data i alpha beta halphaParameter hbetaParameter halpha hbeta hcoords hextent


-- created on 2026-10-23
