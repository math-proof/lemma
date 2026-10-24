import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSScaleTwoAudit
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_scaleTwoAxisGapRestrictedConfig_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSScaleTwoAudit.lean)
-/
@[path]
private lemma rlc_scaleTwoAxisGapRestrictedConfig_failure_eq :
-- imply
  rlc_scaleTwoAxisGapRestrictedConfig ∉ rlc_finiteAxisGapConnectorEvent rlc_scaleTwoDoubleFailureGap := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoAxisGapRestrictedConfig_failure

/--
[rlc_scaleTwoAxisGapRegion_eq_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSScaleTwoAudit.lean)
-/
@[path]
private lemma rlc_scaleTwoAxisGapRegion_eq_singleton_eq :
-- imply
  rlc_axisGapRegion rlc_scaleTwoDoubleFailureGap = {(![0, -1] : Site 2)} := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoAxisGapRegion_eq_singleton

/--
[rlc_scaleTwoAxisGap_westEdge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSScaleTwoAudit.lean)
-/
@[path]
private lemma rlc_scaleTwoAxisGap_westEdge_mem_eq :
-- imply
  s((![-1, -1] : Site 2), ![0, -1]) ∈ rlc_axisGapEdges rlc_scaleTwoDoubleFailureGap := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoAxisGap_westEdge_mem

/--
[rlc_scaleTwoAxisGap_leftEdge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSScaleTwoAudit.lean)
-/
@[path]
private lemma rlc_scaleTwoAxisGap_leftEdge_mem_eq :
-- imply
  s((![0, -1] : Site 2), ![0, 0]) ∈ rlc_axisGapEdges rlc_scaleTwoDoubleFailureGap := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoAxisGap_leftEdge_mem

/--
[rlc_scaleTwoAxisGap_left_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSScaleTwoAudit.lean)
-/
@[path]
private lemma rlc_scaleTwoAxisGap_left_neighbor_eq
  {x y : RlcConnectorVertex 2}
-- given
  (hx : rlc_connectorOnLeft rlc_scaleTwoDoubleFailureLeft x)
  (hxy : (rlc_axisGapFiniteGraph rlc_scaleTwoDoubleFailureGap).Adj x y) :
-- imply
  (x : Site 2) = ![0, 0] ∧ (y : Site 2) = ![0, -1] := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoAxisGap_left_neighbor hx hxy

/--
[rlc_scaleTwoAxisGap_right_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSScaleTwoAudit.lean)
-/
@[path]
private lemma rlc_scaleTwoAxisGap_right_neighbor_eq
  {x y : RlcConnectorVertex 2}
-- given
  (hx : rlc_connectorOnRight rlc_scaleTwoDoubleFailureRight x)
  (hxy : (rlc_axisGapFiniteGraph rlc_scaleTwoDoubleFailureGap).Adj x y) :
-- imply
  ((x : Site 2) = ![0, -2] ∨ (x : Site 2) = ![1, -1]) ∧ (y : Site 2) = ![0, -1] := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoAxisGap_right_neighbor hx hxy

/--
[rlc_scaleTwoAxisGap_failure_of_leftEdge_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSScaleTwoAudit.lean)
-/
@[path]
private lemma rlc_scaleTwoAxisGap_failure_of_leftEdge_closed_eq
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex 2))}
-- given
  (hclosed : rho s(⟨![0, -1], by simp [mem_rect]⟩, ⟨![0, 0], by simp [mem_rect]⟩) = false) :
-- imply
  rho ∉ rlc_finiteAxisGapConnectorEvent rlc_scaleTwoDoubleFailureGap := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoAxisGap_failure_of_leftEdge_closed rho hclosed

/--
[rlc_scaleTwoAxisGapDoubleFailureConfig_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSScaleTwoAudit.lean)
-/
@[path]
private lemma rlc_scaleTwoAxisGapDoubleFailureConfig_failure_eq :
-- imply
  rlc_scaleTwoAxisGapDoubleFailureConfig ∉ rlc_finiteAxisGapConnectorEvent rlc_scaleTwoDoubleFailureGap := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoAxisGapDoubleFailureConfig_failure

/--
[rlc_scaleTwoAxisGapDoubleFailureConfig_PIMS_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSScaleTwoAudit.lean)
-/
@[path]
private lemma rlc_scaleTwoAxisGapDoubleFailureConfig_PIMS_failure_eq :
-- imply
  rlc_axisGapPIMSReflectedConfig rlc_scaleTwoDoubleFailureGap rlc_scaleTwoAxisGapDoubleFailureConfig ∉ rlc_finiteAxisGapConnectorEvent rlc_scaleTwoDoubleFailureGap := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoAxisGapDoubleFailureConfig_PIMS_failure

/--
[rlc_scaleTwoAxisGap_doubleFailure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSScaleTwoAudit.lean)
-/
@[path]
private lemma rlc_scaleTwoAxisGap_doubleFailure_eq :
-- imply
  rlc_scaleTwoAxisGapDoubleFailureConfig ∉ rlc_finiteAxisGapConnectorEvent rlc_scaleTwoDoubleFailureGap ∧ rlc_axisGapPIMSReflectedConfig rlc_scaleTwoDoubleFailureGap rlc_scaleTwoAxisGapDoubleFailureConfig ∉ rlc_finiteAxisGapConnectorEvent rlc_scaleTwoDoubleFailureGap := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoAxisGap_doubleFailure

/--
[rlc_scaleTwoAxisGap_not_failureSelectedSideTopology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSScaleTwoAudit.lean)
-/
@[path]
private lemma rlc_scaleTwoAxisGap_not_failureSelectedSideTopology_eq :
-- imply
  ¬ RlcAxisGapPIMSFailureSelectedSideTopology rlc_scaleTwoDoubleFailureGap (by norm_num) (by norm_num [rlc_scaleTwoDoubleFailureGap]) := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoAxisGap_not_failureSelectedSideTopology


-- created on 2026-10-23
