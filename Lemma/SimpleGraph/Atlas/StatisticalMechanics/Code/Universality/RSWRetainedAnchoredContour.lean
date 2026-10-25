import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWRetainedAnchoredContour.Part4
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_retainedFailureAnchoredContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRetainedAnchoredContour.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_retainedFailureAnchoredContour_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (h : RlcRetainedFailureAnchoredContour G omega) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_retainedFailureAnchoredContour G hn hlt omega h

/--
[rlc_dualReflect_success_of_failureSelectedExtremalTraceTopology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRetainedAnchoredContour.lean)
-/
@[path]
private lemma rlc_dualReflect_success_of_failureSelectedExtremalTraceTopology_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (htopology : RlcFailureSelectedExtremalTraceTopology G)
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_dualReflect_success_of_failureSelectedExtremalTraceTopology G hn hlt htopology omega hno

/--
[rlc_mixedWiredConnector_half_of_failureSelectedExtremalTraceTopology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRetainedAnchoredContour.lean)
-/
@[path]
private lemma rlc_mixedWiredConnector_half_of_failureSelectedExtremalTraceTopology_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (htopology : RlcFailureSelectedExtremalTraceTopology G) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (rlc_mixedWiredConnectorEvent G) := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnector_half_of_failureSelectedExtremalTraceTopology G hn hlt htopology

/--
[rlc_traceSplitCounterexample_fullBoundaryCycle_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRetainedAnchoredContour.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_fullBoundaryCycle_isCycle_eq :
-- imply
  rlc_traceSplitCounterexample_fullBoundaryCycle.IsCycle := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_fullBoundaryCycle_isCycle

/--
[rlc_traceSplitCounterexample_fullBoundaryCycle_carriesContactArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRetainedAnchoredContour.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_fullBoundaryCycle_carriesContactArc_eq :
-- imply
  RlcFaceBoundaryWalkCarriesRelaxedTraceArc rlc_windingSideCounterexampleGap rlc_windingSideCounterexampleConfig rlc_traceSplitCounterexample_fullBoundaryCycle := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_fullBoundaryCycle_carriesContactArc

/--
[rlc_windingSideCounterexample_dual_success_via_retainedContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRetainedAnchoredContour.lean)
-/
@[path]
private lemma rlc_windingSideCounterexample_dual_success_via_retainedContour_eq :
-- imply
  rlc_dualReflectConfig rlc_windingSideCounterexampleConfig ∈ rlc_mixedWiredConnectorEvent rlc_windingSideCounterexampleGap := by
-- proof
  apply StatMech.Universality.rlc_windingSideCounterexample_dual_success_via_retainedContour


-- created on 2026-10-23
