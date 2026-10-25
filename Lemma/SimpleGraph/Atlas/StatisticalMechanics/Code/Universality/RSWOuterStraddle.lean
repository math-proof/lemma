import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.Universality.RSWOuterStraddle.Part2
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_traceStraddlesLoop_of_endpointSides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterStraddle.lean)
-/
@[path]
private lemma rlc_traceStraddlesLoop_of_endpointSides_eq
  {a b c d : ℤ}
  {u : Site 2}
  {C : (hypercubicLattice 2).Walk u u}
  {gamma : RlcCrossingPath a b c d}
-- given
  (h : rlc_OppositeLoopSides C (gamma.1 : Site 2) (gamma.2.1 : Site 2)) :
-- imply
  rlc_TraceStraddlesLoop C gamma := by
-- proof
  apply StatMech.Universality.rlc_traceStraddlesLoop_of_endpointSides C gamma h

/--
[rlc_mixedWiredReachSet_separates_traceEndpoints_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterStraddle.lean)
-/
@[path]
private lemma rlc_mixedWiredReachSet_separates_traceEndpoints_of_failure_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
-- imply
  (gamma.1.1 : Site 2) ∈ rlc_mixedWiredReachSet G omega ∧ (gamma.1.2.1 : Site 2) ∈ rlc_mixedWiredReachSet G omega ∧ (gamma'.1.1 : Site 2) ∉ rlc_mixedWiredReachSet G omega ∧ (gamma'.1.2.1 : Site 2) ∉ rlc_mixedWiredReachSet G omega := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredReachSet_separates_traceEndpoints_of_failure G omega hno

/--
[rlc_outerExit_both_straddles_of_endpointSides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterStraddle.lean)
-/
@[path]
private lemma rlc_outerExit_both_straddles_of_endpointSides_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (h : RlcOuterExitEndpointSides G hn hlt omega) :
-- imply
  rlc_TraceStraddlesLoop ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe (rlc_openSubgraph_le_lattice _)) gamma.1 ∧ rlc_TraceStraddlesLoop ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe (rlc_openSubgraph_le_lattice _)) gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_outerExit_both_straddles_of_endpointSides G hn hlt omega h

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_outerExitEndpointSides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterStraddle.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_outerExitEndpointSides_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hsides : RlcOuterExitEndpointSides G hn hlt omega)
  (horder : RlcOuterExitContactArcOrder G omega) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_outerExitEndpointSides G hn hlt omega hsides horder

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_outerExitGoodContactPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterStraddle.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_outerExitGoodContactPair_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (h : RlcOuterExitGoodContactPair G omega) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_outerExitGoodContactPair G hn hlt omega h


-- created on 2026-10-23
