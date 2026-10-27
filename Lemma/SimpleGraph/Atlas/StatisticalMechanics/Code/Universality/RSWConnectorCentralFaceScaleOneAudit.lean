import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceScaleOneAudit.Part2
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_axisReturnCounterexample_left_vertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceScaleOneAudit.lean)
-/
@[path]
private lemma rlc_axisReturnCounterexample_left_vertices_eq :
-- imply
  rlc_pathVertices rlc_axisReturnCounterexampleLeft.1 = {![-2, 0], ![-2, 1], ![-1, 1], ![-1, 0], ![0, 0], ![0, 1]} := by
-- proof
  apply StatMech.Universality.rlc_axisReturnCounterexample_left_vertices

/--
[rlc_axisReturnCounterexample_left_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceScaleOneAudit.lean)
-/
@[path]
private lemma rlc_axisReturnCounterexample_left_edges_eq :
-- imply
  rlc_pathEdges rlc_axisReturnCounterexampleLeft.1 = {s((![-2, 0] : Site 2), ![-2, 1]), s((![-2, 1] : Site 2), ![-1, 1]), s((![-1, 1] : Site 2), ![-1, 0]), s((![-1, 0] : Site 2), ![0, 0]), s((![0, 0] : Site 2), ![0, 1])} := by
-- proof
  apply StatMech.Universality.rlc_axisReturnCounterexample_left_edges

/--
[rlc_axisReturnCounterexample_bookPositioned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceScaleOneAudit.lean)
-/
@[path]
private lemma rlc_axisReturnCounterexample_bookPositioned_eq :
-- imply
  RlcBookPositionedTracePair rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft := by
-- proof
  apply StatMech.Universality.rlc_axisReturnCounterexample_bookPositioned

/--
[rlc_axisReturnCounterexample_not_bookFaithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceScaleOneAudit.lean)
-/
@[path]
private lemma rlc_axisReturnCounterexample_not_bookFaithful_eq :
-- imply
  ¬ RlcBookFaithfulTracePair rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft := by
-- proof
  apply StatMech.Universality.rlc_axisReturnCounterexample_not_bookFaithful

/--
[rlc_bookPositioned_not_imply_bookFaithful_scaleOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceScaleOneAudit.lean)
-/
@[path]
private lemma rlc_bookPositioned_not_imply_bookFaithful_scaleOne_eq :
-- imply
  ¬ (RlcBookPositionedTracePair rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft -> RlcBookFaithfulTracePair rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft) := by
-- proof
  apply StatMech.Universality.rlc_bookPositioned_not_imply_bookFaithful_scaleOne

/--
[rlc_traceSplitCounterexample_bookFaithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceScaleOneAudit.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_bookFaithful_eq :
-- imply
  RlcBookFaithfulTracePair rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_bookFaithful

/--
[rlc_traceSplitCounterexample_bookFaithfulExtremal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceScaleOneAudit.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_bookFaithfulExtremal_eq :
-- imply
  RlcBookFaithfulExtremalTracePair rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_bookFaithfulExtremal

/--
[rlc_activeDoubleFailure_centralFaceClosurePIMS_success](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceScaleOneAudit.lean)
-/
@[path]
private lemma rlc_activeDoubleFailure_centralFaceClosurePIMS_success_eq :
-- imply
  rlc_connectorCentralFacePIMSConfig rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft rlc_activeGapDoubleFailureConfig ∈ rlc_finiteCentralFaceClosureConnectorEvent rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
-- proof
  apply StatMech.Universality.rlc_activeDoubleFailure_centralFaceClosurePIMS_success


-- created on 2026-10-23
