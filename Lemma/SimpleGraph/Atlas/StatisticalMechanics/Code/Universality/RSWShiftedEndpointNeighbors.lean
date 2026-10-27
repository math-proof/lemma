import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWShiftedEndpointNeighbors.Part3
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_right_start_shiftedPreimage_not_mem_of_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWShiftedEndpointNeighbors.lean)
-/
@[path]
private lemma rlc_right_start_shiftedPreimage_not_mem_of_bottom_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
-- given
  (hbottom : (gamma.1.1 : Site 2) 1 = -n) :
-- imply
  rlc_shiftedEndpointPreimage (gamma.1.1 : Site 2) ∉ rlc_pathVertices gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_right_start_shiftedPreimage_not_mem_of_bottom gamma hbottom

/--
[rlc_not_shiftedEndpointTraceNeighbors_of_right_start_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWShiftedEndpointNeighbors.lean)
-/
@[path]
private lemma rlc_not_shiftedEndpointTraceNeighbors_of_right_start_bottom_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hbottom : (gamma.1.1 : Site 2) 1 = -n) :
-- imply
  ¬ RlcShiftedEndpointTraceNeighbors gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_not_shiftedEndpointTraceNeighbors_of_right_start_bottom gamma gamma' hbottom

/--
[rlc_shiftedNeighborCounterexampleRight_start_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWShiftedEndpointNeighbors.lean)
-/
@[path]
private lemma rlc_shiftedNeighborCounterexampleRight_start_one_eq :
-- imply
  (rlc_shiftedNeighborCounterexampleRight.1.1 : Site 2) 1 = -1 := by
-- proof
  apply StatMech.Universality.rlc_shiftedNeighborCounterexampleRight_start_one

/--
[rlc_shiftedEndpointTraceNeighbors_counterexample](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWShiftedEndpointNeighbors.lean)
-/
@[path]
private lemma rlc_shiftedEndpointTraceNeighbors_counterexample_eq :
-- imply
  ¬ RlcShiftedEndpointTraceNeighbors rlc_shiftedNeighborCounterexampleRight (rlc_rot180RightPath rlc_shiftedNeighborCounterexampleRight) := by
-- proof
  apply StatMech.Universality.rlc_shiftedEndpointTraceNeighbors_counterexample


-- created on 2026-10-23
