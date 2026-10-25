import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWAxisOrContactObstruction.Part2
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_axisOrContactCounterexampleConfig_eq_true_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisOrContactObstruction.lean)
-/
@[path]
private lemma rlc_axisOrContactCounterexampleConfig_eq_true_iff_eq
  {e : Sym2 (Site 2)} :
-- imply
  rlc_axisOrContactCounterexampleConfig e = true ↔ e = rlc_axisOrContactCounterexampleEdge := by
-- proof
  apply StatMech.Universality.rlc_axisOrContactCounterexampleConfig_eq_true_iff e

/--
[rlc_axisOrContactCounterexampleConfig_special](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisOrContactObstruction.lean)
-/
@[path]
private lemma rlc_axisOrContactCounterexampleConfig_special_eq :
-- imply
  rlc_axisOrContactCounterexampleConfig rlc_axisOrContactCounterexampleEdge = true := by
-- proof
  apply StatMech.Universality.rlc_axisOrContactCounterexampleConfig_special

/--
[rlc_axisOrContactCounterexample_reachSet_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisOrContactObstruction.lean)
-/
@[path]
private lemma rlc_axisOrContactCounterexample_reachSet_eq_eq :
-- imply
  rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap rlc_axisOrContactCounterexampleConfig = (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2)) := by
-- proof
  apply StatMech.Universality.rlc_axisOrContactCounterexample_reachSet_eq

/--
[rlc_axisOrContactCounterexample_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisOrContactObstruction.lean)
-/
@[path]
private lemma rlc_axisOrContactCounterexample_failure_eq :
-- imply
  rlc_axisOrContactCounterexampleConfig ∉ rlc_mixedWiredConnectorEvent rlc_windingSideCounterexampleGap := by
-- proof
  apply StatMech.Universality.rlc_axisOrContactCounterexample_failure

/--
[rlc_axisOrContactCounterexample_not_reflectedBoundaryContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisOrContactObstruction.lean)
-/
@[path]
private lemma rlc_axisOrContactCounterexample_not_reflectedBoundaryContact_eq :
-- imply
  ¬ RlcLowestHighestReflectedBoundaryContact rlc_windingSideCounterexampleGap rlc_axisOrContactCounterexampleConfig := by
-- proof
  apply StatMech.Universality.rlc_axisOrContactCounterexample_not_reflectedBoundaryContact

/--
[rlc_axisOrContactCounterexample_not_axisClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisOrContactObstruction.lean)
-/
@[path]
private lemma rlc_axisOrContactCounterexample_not_axisClosed_eq :
-- imply
  ¬ RlcAxisGapPIMSPreimagesClosed rlc_windingSideCounterexampleGap rlc_axisOrContactCounterexampleConfig := by
-- proof
  apply StatMech.Universality.rlc_axisOrContactCounterexample_not_axisClosed

/--
[rlc_axisOrContactCounterexample_not_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisOrContactObstruction.lean)
-/
@[path]
private lemma rlc_axisOrContactCounterexample_not_certificate_eq :
-- imply
  ¬ RlcAxisOrContactDualConnectorCertificate rlc_windingSideCounterexampleGap rlc_axisOrContactCounterexampleConfig := by
-- proof
  apply StatMech.Universality.rlc_axisOrContactCounterexample_not_certificate

/--
[rlc_failure_not_imply_axisOrContact_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisOrContactObstruction.lean)
-/
@[path]
private lemma rlc_failure_not_imply_axisOrContact_certificate_eq :
-- imply
  ¬ (∀ omega : ConfigSpace (Sym2 (Site 2)), omega ∉ rlc_mixedWiredConnectorEvent rlc_windingSideCounterexampleGap → RlcAxisOrContactDualConnectorCertificate rlc_windingSideCounterexampleGap omega) := by
-- proof
  apply StatMech.Universality.rlc_failure_not_imply_axisOrContact_certificate

/--
[rlc_mixedWiredFailure_reflectedAnchor_raw_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisOrContactObstruction.lean)
-/
@[path]
private lemma rlc_mixedWiredFailure_reflectedAnchor_raw_walk_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
-- imply
  ∃ (t : ℤ) (p : (openSubgraph 2 (rlc_dualReflectConfig omega)).Walk ![-1, t + 1] ![0, t + 1]), G.lower ≤ t ∧ t < G.upper ∧ p.length = 1 := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredFailure_reflectedAnchor_raw_walk G hn hlt omega hno

/--
[rlc_dualReflect_singleClosedFailureAnchor_eq_true_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisOrContactObstruction.lean)
-/
@[path]
private lemma rlc_dualReflect_singleClosedFailureAnchor_eq_true_iff_eq
  {t : ℤ}
  {e : Sym2 (Site 2)} :
-- imply
  rlc_dualReflectConfig (rlc_singleClosedFailureAnchorConfig t) e = true ↔ e = rlc_reflectedFailureAnchorEdge t := by
-- proof
  apply StatMech.Universality.rlc_dualReflect_singleClosedFailureAnchor_eq_true_iff t e

/--
[rlc_singleClosedFailureAnchor_raw_reachable_only_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisOrContactObstruction.lean)
-/
@[path]
private lemma rlc_singleClosedFailureAnchor_raw_reachable_only_endpoints_eq
  {t : ℤ}
  {z : Site 2}
-- given
  (hreach : (openSubgraph 2 (rlc_dualReflectConfig (rlc_singleClosedFailureAnchorConfig t))).Reachable ![-1, t + 1] z) :
-- imply
  z = ![-1, t + 1] ∨ z = ![0, t + 1] := by
-- proof
  apply StatMech.Universality.rlc_singleClosedFailureAnchor_raw_reachable_only_endpoints t hreach

/--
[rlc_singleClosedFailureAnchor_no_raw_extension](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisOrContactObstruction.lean)
-/
@[path]
private lemma rlc_singleClosedFailureAnchor_no_raw_extension_eq
  {t : ℤ} :
-- imply
  ¬ (openSubgraph 2 (rlc_dualReflectConfig (rlc_singleClosedFailureAnchorConfig t))).Reachable ![-1, t + 1] ![1, t + 1] := by
-- proof
  apply StatMech.Universality.rlc_singleClosedFailureAnchor_no_raw_extension t


-- created on 2026-10-23
