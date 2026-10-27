import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWTraceSeparationObstruction.Part2
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_traceSplitCounterexample_right_vertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceSeparationObstruction.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_right_vertices_eq :
-- imply
  rlc_pathVertices rlc_traceSplitCounterexampleRight.1 = {![0, -1], ![1, -1], ![2, -1], ![2, 0]} := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_right_vertices

/--
[rlc_traceSplitCounterexample_right_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceSeparationObstruction.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_right_edges_eq :
-- imply
  rlc_pathEdges rlc_traceSplitCounterexampleRight.1 = {s((![0, -1] : Site 2), ![1, -1]), s((![1, -1] : Site 2), ![2, -1]), s((![2, -1] : Site 2), ![2, 0])} := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_right_edges

/--
[rlc_traceSplitCounterexample_left_vertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceSeparationObstruction.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_left_vertices_eq :
-- imply
  rlc_pathVertices rlc_traceSplitCounterexampleLeft.1 = {![-2, 0], ![-2, 1], ![-1, 1], ![0, 1]} := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_left_vertices

/--
[rlc_traceSplitCounterexample_left_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceSeparationObstruction.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_left_edges_eq :
-- imply
  rlc_pathEdges rlc_traceSplitCounterexampleLeft.1 = {s((![-2, 0] : Site 2), ![-2, 1]), s((![-2, 1] : Site 2), ![-1, 1]), s((![-1, 1] : Site 2), ![0, 1])} := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_left_edges

/--
[rlc_traceSplitCounterexample_right_preimage_avoids_traces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceSeparationObstruction.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_right_preimage_avoids_traces_eq
  {x : Site 2}
-- given
  (hx : x ∈ rlc_pathVertices rlc_traceSplitCounterexampleRight.1) :
-- imply
  rlc_primalDualReflect.symm x ∉ rlc_pathVertices rlc_traceSplitCounterexampleRight.1 ∧ rlc_primalDualReflect.symm x ∉ rlc_pathVertices rlc_traceSplitCounterexampleLeft.1 := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_right_preimage_avoids_traces hx

/--
[rlc_tracePreimagesSplit_counterexample_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceSeparationObstruction.lean)
-/
@[path]
private lemma rlc_tracePreimagesSplit_counterexample_right_eq :
-- imply
  ¬ RlcTracePreimagesSplit rlc_traceSplitCounterexampleRight.1 rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
-- proof
  apply StatMech.Universality.rlc_tracePreimagesSplit_counterexample_right

/--
[rlc_lowestHighestTracePreimageSplit_counterexample](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceSeparationObstruction.lean)
-/
@[path]
private lemma rlc_lowestHighestTracePreimageSplit_counterexample_eq :
-- imply
  ¬ RlcLowestHighestTracePreimageSplit rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
-- proof
  apply StatMech.Universality.rlc_lowestHighestTracePreimageSplit_counterexample


-- created on 2026-10-23
