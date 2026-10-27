import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWFailureComplementaryArcObstruction.Part8
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_scaleTwoDoubleFailure_right_vertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureComplementaryArcObstruction.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailure_right_vertices_eq :
-- imply
  rlc_pathVertices rlc_scaleTwoDoubleFailureRight.1 = {![0, -2], ![1, -2], ![1, -1], ![2, -1], ![3, -1], ![4, -1], ![4, 0]} := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailure_right_vertices

/--
[rlc_scaleTwoDoubleFailure_left_vertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureComplementaryArcObstruction.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailure_left_vertices_eq :
-- imply
  rlc_pathVertices rlc_scaleTwoDoubleFailureLeft.1 = {![-4, -2], ![-3, -2], ![-2, -2], ![-2, -1], ![-2, 0], ![-1, 0], ![0, 0]} := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailure_left_vertices

/--
[rlc_scaleTwoDoubleFailure_right_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureComplementaryArcObstruction.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailure_right_edges_eq :
-- imply
  rlc_pathEdges rlc_scaleTwoDoubleFailureRight.1 = {s(![0, -2], ![1, -2]), s(![1, -2], ![1, -1]), s(![1, -1], ![2, -1]), s(![2, -1], ![3, -1]), s(![3, -1], ![4, -1]), s(![4, -1], ![4, 0])} := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailure_right_edges

/--
[rlc_scaleTwoDoubleFailure_left_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureComplementaryArcObstruction.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailure_left_edges_eq :
-- imply
  rlc_pathEdges rlc_scaleTwoDoubleFailureLeft.1 = {s(![-4, -2], ![-3, -2]), s(![-3, -2], ![-2, -2]), s(![-2, -2], ![-2, -1]), s(![-2, -1], ![-2, 0]), s(![-2, 0], ![-1, 0]), s(![-1, 0], ![0, 0])} := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailure_left_edges

/--
[rlc_scaleTwoDoubleFailureConfig_eq_true_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureComplementaryArcObstruction.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailureConfig_eq_true_iff_eq
  {e : Sym2 (Site 2)} :
-- imply
  rlc_scaleTwoDoubleFailureConfig e = true ↔ e ∈ rlc_scaleTwoDoubleFailureOpenEdges := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailureConfig_eq_true_iff e

/--
[rlc_scaleTwoDoubleFailure_original_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureComplementaryArcObstruction.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailure_original_failure_eq :
-- imply
  rlc_scaleTwoDoubleFailureConfig ∉ rlc_mixedWiredConnectorEvent rlc_scaleTwoDoubleFailureGap := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailure_original_failure

/--
[rlc_scaleTwoDoubleFailure_reflected_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureComplementaryArcObstruction.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailure_reflected_failure_eq :
-- imply
  rlc_dualReflectConfig rlc_scaleTwoDoubleFailureConfig ∉ rlc_mixedWiredConnectorEvent rlc_scaleTwoDoubleFailureGap := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailure_reflected_failure

/--
[rlc_scaleTwoDoubleFailure_defectCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureComplementaryArcObstruction.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailure_defectCut_eq :
-- imply
  RlcRelaxedLocalDefectsSeparateTraces rlc_scaleTwoDoubleFailureGap rlc_scaleTwoDoubleFailureConfig := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailure_defectCut

/--
[rlc_scaleTwoDoubleFailure_no_relaxedLocalTraceArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureComplementaryArcObstruction.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailure_no_relaxedLocalTraceArc_eq :
-- imply
  ¬ RlcRelaxedLocalTraceArcExists rlc_scaleTwoDoubleFailureGap rlc_scaleTwoDoubleFailureConfig := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailure_no_relaxedLocalTraceArc

/--
[rlc_scaleTwoDoubleFailure_not_failureComplementaryArcEscapes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureComplementaryArcObstruction.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailure_not_failureComplementaryArcEscapes_eq :
-- imply
  ¬ RlcFailureComplementaryArcEscapesDefectCut rlc_scaleTwoDoubleFailureGap rlc_scaleTwoDoubleFailureConfig := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailure_not_failureComplementaryArcEscapes

/--
[rlc_scaleTwoDoubleFailure_not_failureSelectedExtremalTraceTopology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureComplementaryArcObstruction.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailure_not_failureSelectedExtremalTraceTopology_eq :
-- imply
  ¬ RlcFailureSelectedExtremalTraceTopology rlc_scaleTwoDoubleFailureGap := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailure_not_failureSelectedExtremalTraceTopology

/--
[rlc_failure_not_imply_failureComplementaryArcEscapesDefectCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureComplementaryArcObstruction.lean)
-/
@[path]
private lemma rlc_failure_not_imply_failureComplementaryArcEscapesDefectCut_eq :
-- imply
  ¬ (∀ omega : ConfigSpace (Sym2 (Site 2)), omega ∉ rlc_mixedWiredConnectorEvent rlc_scaleTwoDoubleFailureGap → RlcFailureComplementaryArcEscapesDefectCut rlc_scaleTwoDoubleFailureGap omega) := by
-- proof
  apply StatMech.Universality.rlc_failure_not_imply_failureComplementaryArcEscapesDefectCut


-- created on 2026-10-23
