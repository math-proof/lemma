import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.RSWFailureSelectedCarryObstruction
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_traceSplitCounterexample_anchor_mem_of_relaxedTraceArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureSelectedCarryObstruction.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_anchor_mem_of_relaxedTraceArc_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2}
  {a : (faceBoundaryGraph (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega)).Walk x y}
-- given
  (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega = (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2)))
  (hx : rlc_dualReflect x ∈ rlc_pathVertices rlc_traceSplitCounterexampleRight.1)
  (hy : rlc_dualReflect y ∈ rlc_pathVertices rlc_traceSplitCounterexampleLeft.1)
  (hlocal : ∀ {f g : Site 2}, s(f, g) ∈ a.edges → rlc_contourEdgeRelaxedLocal rlc_windingSideCounterexampleGap f g) :
-- imply
  rlc_traceSplitCounterexample_failureAnchor ∈ a.edges := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_anchor_mem_of_relaxedTraceArc omega hK a hx hy hlocal

/--
[rlc_traceSplitCounterexample_not_carries_of_anchor_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureSelectedCarryObstruction.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_not_carries_of_anchor_not_mem_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {u v : Site 2}
  {p : (faceBoundaryGraph (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega)).Walk u v}
-- given
  (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega = (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2)))
  (hanchor : rlc_traceSplitCounterexample_failureAnchor ∉ p.edges) :
-- imply
  ¬ RlcFaceBoundaryWalkCarriesRelaxedTraceArc rlc_windingSideCounterexampleGap omega p := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_not_carries_of_anchor_not_mem omega hK p hanchor

/--
[rlc_windingSideCounterexample_not_failureComplementaryArcEscapes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureSelectedCarryObstruction.lean)
-/
@[path]
private lemma rlc_windingSideCounterexample_not_failureComplementaryArcEscapes_eq :
-- imply
  ¬ RlcFailureComplementaryArcEscapesDefectCut rlc_windingSideCounterexampleGap rlc_windingSideCounterexampleConfig := by
-- proof
  apply StatMech.Universality.rlc_windingSideCounterexample_not_failureComplementaryArcEscapes

/--
[rlc_windingSideCounterexample_failure_selected_obstruction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureSelectedCarryObstruction.lean)
-/
@[path]
private lemma rlc_windingSideCounterexample_failure_selected_obstruction_eq :
-- imply
  rlc_windingSideCounterexampleConfig ∉ rlc_mixedWiredConnectorEvent rlc_windingSideCounterexampleGap ∧ ¬ RlcFailureComplementaryArcEscapesDefectCut rlc_windingSideCounterexampleGap rlc_windingSideCounterexampleConfig ∧ RlcRelaxedLocalTraceArcExists rlc_windingSideCounterexampleGap rlc_windingSideCounterexampleConfig := by
-- proof
  apply StatMech.Universality.rlc_windingSideCounterexample_failure_selected_obstruction


-- created on 2026-10-23
