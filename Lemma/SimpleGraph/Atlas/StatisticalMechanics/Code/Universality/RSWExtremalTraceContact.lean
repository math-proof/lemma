import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_ambientCrossingWalk_edge_mem_pathEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWExtremalTraceContact.lean)
-/
@[path]
private lemma rlc_ambientCrossingWalk_edge_mem_pathEdges_eq
  {a b c d : ℤ}
  {tau : RlcCrossingPath a b c d}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ (rlc_ambientCrossingWalk tau).edges) :
-- imply
  e ∈ rlc_pathEdges tau := by
-- proof
  apply StatMech.Universality.rlc_ambientCrossingWalk_edge_mem_pathEdges tau he

/--
[rlc_tracePreimageRegionSplit_iff_reflectedBoundaryContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWExtremalTraceContact.lean)
-/
@[path]
private lemma rlc_tracePreimageRegionSplit_iff_reflectedBoundaryContact_eq
  {a b c d : ℤ}
  {tau : RlcCrossingPath a b c d}
  {K : Set (Site 2)} :
-- imply
  RlcTracePreimageRegionSplit tau K ↔ RlcTraceReflectedBoundaryContact tau K := by
-- proof
  apply StatMech.Universality.rlc_tracePreimageRegionSplit_iff_reflectedBoundaryContact tau K

/--
[rlc_outerExitTraceWindingSplit_iff_reflectedBoundaryContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWExtremalTraceContact.lean)
-/
@[path]
private lemma rlc_outerExitTraceWindingSplit_iff_reflectedBoundaryContact_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  RlcOuterExitTraceWindingSplit G omega ↔ RlcLowestHighestReflectedBoundaryContact G omega := by
-- proof
  apply StatMech.Universality.rlc_outerExitTraceWindingSplit_iff_reflectedBoundaryContact G omega

/--
[rlc_outerExitTraceSeparation_of_reflectedBoundaryContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWExtremalTraceContact.lean)
-/
@[path]
private lemma rlc_outerExitTraceSeparation_of_reflectedBoundaryContact_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hcontact : RlcLowestHighestReflectedBoundaryContact G omega) :
-- imply
  RlcOuterExitTraceSeparation G hn hlt omega := by
-- proof
  apply StatMech.Universality.rlc_outerExitTraceSeparation_of_reflectedBoundaryContact G hn hlt omega hcontact

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_boundaryContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWExtremalTraceContact.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_boundaryContact_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hcontact : RlcLowestHighestReflectedBoundaryContact G omega)
  (horder : RlcOuterExitContactArcOrder G omega) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_boundaryContact G hn hlt omega hcontact horder

/--
[rlc_windingSideCounterexample_not_reflectedBoundaryContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWExtremalTraceContact.lean)
-/
@[path]
private lemma rlc_windingSideCounterexample_not_reflectedBoundaryContact_eq :
-- imply
  ¬ RlcLowestHighestReflectedBoundaryContact rlc_windingSideCounterexampleGap rlc_windingSideCounterexampleConfig := by
-- proof
  apply StatMech.Universality.rlc_windingSideCounterexample_not_reflectedBoundaryContact


-- created on 2026-10-23
