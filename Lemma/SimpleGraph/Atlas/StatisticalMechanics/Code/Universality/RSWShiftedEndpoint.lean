import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWShiftedEndpoint.Part3
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_shiftedEndpointPreimage_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWShiftedEndpoint.lean)
-/
@[path]
private lemma rlc_shiftedEndpointPreimage_zero_eq
  {x : Site 2} :
-- imply
  rlc_shiftedEndpointPreimage x 0 = -x 0 := by
-- proof
  apply StatMech.Universality.rlc_shiftedEndpointPreimage_zero x

/--
[rlc_shiftedEndpointPreimage_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWShiftedEndpoint.lean)
-/
@[path]
private lemma rlc_shiftedEndpointPreimage_one_eq
  {x : Site 2} :
-- imply
  rlc_shiftedEndpointPreimage x 1 = x 1 - 1 := by
-- proof
  apply StatMech.Universality.rlc_shiftedEndpointPreimage_one x

/--
[rlc_right_end_shiftedPreimage_not_mem_rightPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWShiftedEndpoint.lean)
-/
@[path]
private lemma rlc_right_end_shiftedPreimage_not_mem_rightPath_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  rlc_shiftedEndpointPreimage (gamma.1.2.1 : Site 2) ∉ rlc_pathVertices gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_right_end_shiftedPreimage_not_mem_rightPath hn gamma

/--
[rlc_left_start_shiftedPreimage_not_mem_leftPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWShiftedEndpoint.lean)
-/
@[path]
private lemma rlc_left_start_shiftedPreimage_not_mem_leftPath_eq
  {n : ℤ}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  rlc_shiftedEndpointPreimage (gamma'.1.1 : Site 2) ∉ rlc_pathVertices gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_left_start_shiftedPreimage_not_mem_leftPath hn gamma'

/--
[rlc_shiftedEndpointTraceNeighbors_iff_coordinates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWShiftedEndpoint.lean)
-/
@[path]
private lemma rlc_shiftedEndpointTraceNeighbors_iff_coordinates_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  RlcShiftedEndpointTraceNeighbors gamma gamma' ↔ ![-(gamma.1.1 : Site 2) 0, (gamma.1.1 : Site 2) 1 - 1] ∈ rlc_pathVertices gamma.1 ∧ ![-(gamma.1.2.1 : Site 2) 0, (gamma.1.2.1 : Site 2) 1 - 1] ∈ rlc_pathVertices gamma'.1 ∧ ![-(gamma'.1.1 : Site 2) 0, (gamma'.1.1 : Site 2) 1 - 1] ∈ rlc_pathVertices gamma.1 ∧ ![-(gamma'.1.2.1 : Site 2) 0, (gamma'.1.2.1 : Site 2) 1 - 1] ∈ rlc_pathVertices gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_shiftedEndpointTraceNeighbors_iff_coordinates gamma gamma'

/--
[rlc_shiftedEndpointTraceSplit_iff_neighbors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWShiftedEndpoint.lean)
-/
@[path]
private lemma rlc_shiftedEndpointTraceSplit_iff_neighbors_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  RlcShiftedEndpointTraceSplit gamma gamma' ↔ RlcShiftedEndpointTraceNeighbors gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_shiftedEndpointTraceSplit_iff_neighbors hn gamma gamma'

/--
[rlc_reflectedEndpointXor_of_failure_of_shiftedTraceSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWShiftedEndpoint.lean)
-/
@[path]
private lemma rlc_reflectedEndpointXor_of_failure_of_shiftedTraceSplit_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
  (hsplit : RlcShiftedEndpointTraceSplit gamma gamma') :
-- imply
  RlcReflectedEndpointXor gamma gamma' (rlc_mixedWiredReachSet G omega) := by
-- proof
  apply StatMech.Universality.rlc_reflectedEndpointXor_of_failure_of_shiftedTraceSplit G omega hno hsplit

/--
[rlc_reflectedEndpointXor_of_failure_of_shiftedTraceNeighbors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWShiftedEndpoint.lean)
-/
@[path]
private lemma rlc_reflectedEndpointXor_of_failure_of_shiftedTraceNeighbors_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
  (hneighbors : RlcShiftedEndpointTraceNeighbors gamma gamma') :
-- imply
  RlcReflectedEndpointXor gamma gamma' (rlc_mixedWiredReachSet G omega) := by
-- proof
  apply StatMech.Universality.rlc_reflectedEndpointXor_of_failure_of_shiftedTraceNeighbors G hn omega hno hneighbors

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_shiftedTraceNeighbors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWShiftedEndpoint.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_shiftedTraceNeighbors_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
  (hneighbors : RlcShiftedEndpointTraceNeighbors gamma gamma')
  (hregion : rlc_reflectedPrimalRegion (rlc_mixedWiredReachSet G omega) = jec_leftRegion ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe (rlc_openSubgraph_le_lattice _)))
  (horder : RlcOuterExitContactArcOrder G omega) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_shiftedTraceNeighbors G hn hlt omega hno hneighbors hregion horder


-- created on 2026-10-23
