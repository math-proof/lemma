import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceCarrier.Part7
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_mem_fourTraceWallGraph_edgeSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean)
-/
@[path]
private lemma rlc_mem_fourTraceWallGraph_edgeSet_iff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
-- given
  (hlat : e ∈ (hypercubicLattice 2).edgeSet) :
-- imply
  e ∈ (rlc_connectorFourTraceWallGraph gamma gamma').edgeSet ↔ e ∈ rlc_connectorFourTraceEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_mem_fourTraceWallGraph_edgeSet_iff gamma gamma' hlat

/--
[rlc_mem_connectorBarrier_of_mem_fourTraceEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean)
-/
@[path]
private lemma rlc_mem_connectorBarrier_of_mem_fourTraceEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
  {z : Site 2}
-- given
  (he : e ∈ rlc_connectorFourTraceEdges gamma gamma')
  (hz : z ∈ e) :
-- imply
  z ∈ rlc_connectorBarrier gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_mem_connectorBarrier_of_mem_fourTraceEdge gamma gamma' he hz

/--
[rlc_connectorFourTraceFaceCutGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean)
-/
@[path]
private lemma rlc_connectorFourTraceFaceCutGraph_adj_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f g : Site 2} :
-- imply
  (rlc_connectorFourTraceFaceCutGraph gamma gamma').Adj f g ↔ (hypercubicLattice 2).Adj f g ∧ sharedPrimalEdge f g ∉ rlc_connectorFourTraceEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorFourTraceFaceCutGraph_adj gamma gamma' f g

/--
[rlc_connectorCentralFace_mem_faceBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean)
-/
@[path]
private lemma rlc_connectorCentralFace_mem_faceBox_eq
  {n : Int}
-- given
  (hn : 0 < n) :
-- imply
  rlc_connectorCentralFace ∈ rlc_connectorFaceBox n := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFace_mem_faceBox hn

/--
[rlc_connectorCentralFaceRegionSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceRegionSet_finite_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  (rlc_connectorCentralFaceRegionSet gamma gamma').Finite := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceRegionSet_finite gamma gamma'

/--
[rlc_connectorCentralFace_mem_region](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean)
-/
@[path]
private lemma rlc_connectorCentralFace_mem_region_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  rlc_connectorCentralFace ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFace_mem_region gamma gamma' hn

/--
[rlc_connectorCentralFaceRegion_of_cut_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceRegion_of_cut_adj_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f g : Site 2}
-- given
  (hf : f ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hgBox : g ∈ rlc_connectorFaceBox n)
  (hfg : (rlc_connectorFourTraceFaceCutGraph gamma gamma').Adj f g) :
-- imply
  g ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceRegion_of_cut_adj gamma gamma' hf hgBox hfg

/--
[rlc_connectorCentralFaceRegion_of_cut_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceRegion_of_cut_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f g : Site 2}
-- given
  (hf : f ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hfBox : f ∈ rlc_connectorFaceBox n)
  (hgBox : g ∈ rlc_connectorFaceBox n)
  (hfg : (rlc_connectorFiniteFaceCutGraph gamma gamma').Reachable ⟨f, hfBox⟩ ⟨g, hgBox⟩) :
-- imply
  g ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceRegion_of_cut_reachable gamma gamma' hf hfBox hgBox hfg

/--
[rlc_fci_faceEdgeEquiv_symm_mk_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean)
-/
@[path]
private lemma rlc_fci_faceEdgeEquiv_symm_mk_of_adj_eq
  {x y : Site 2}
-- given
  (hxy : (hypercubicLattice 2).Adj x y) :
-- imply
  fci_faceEdgeEquiv.symm s(x, y) = flankFaces x y := by
-- proof
  apply StatMech.Universality.rlc_fci_faceEdgeEquiv_symm_mk_of_adj hxy

/--
[rlc_mem_connectorCentralFaceClosureEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean)
-/
@[path]
private lemma rlc_mem_connectorCentralFaceClosureEdges_iff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y : Site 2}
-- given
  (hxy : (hypercubicLattice 2).Adj x y) :
-- imply
  s(x, y) ∈ rlc_connectorCentralFaceClosureEdges gamma gamma' ↔ x ∈ rlc_connectorBox n ∧ y ∈ rlc_connectorBox n ∧ ∃ f ∈ rlc_connectorCentralFaceRegion gamma gamma', f ∈ flankFaces x y := by
-- proof
  apply StatMech.Universality.rlc_mem_connectorCentralFaceClosureEdges_iff gamma gamma' hxy

/--
[rlc_mem_connectorCentralFacePlanarEdges_of_box_region_flank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean)
-/
@[path]
private lemma rlc_mem_connectorCentralFacePlanarEdges_of_box_region_flank_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y : Site 2}
  {f : Site 2}
-- given
  (hxy : (hypercubicLattice 2).Adj x y)
  (hx : x ∈ rlc_connectorBox n)
  (hy : y ∈ rlc_connectorBox n)
  (hf : f ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hflank : f ∈ flankFaces x y) :
-- imply
  s(x, y) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_mem_connectorCentralFacePlanarEdges_of_box_region_flank gamma gamma' hxy hx hy hf hflank

/--
[rlc_mem_connectorCentralFacePlanarEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean)
-/
@[path]
private lemma rlc_mem_connectorCentralFacePlanarEdges_iff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y : Site 2}
-- given
  (hxy : (hypercubicLattice 2).Adj x y) :
-- imply
  s(x, y) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' ↔ s(x, y) ∈ rlc_connectorFourTraceEdges gamma gamma' ∨ (x ∈ rlc_connectorBox n ∧ y ∈ rlc_connectorBox n ∧ ∃ f ∈ rlc_connectorCentralFaceRegion gamma gamma', f ∈ flankFaces x y) := by
-- proof
  apply StatMech.Universality.rlc_mem_connectorCentralFacePlanarEdges_iff gamma gamma' hxy

/--
[rlc_connectorCentralFaceEdges_eq_sdiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceEdges_eq_sdiff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  rlc_connectorCentralFaceEdges gamma gamma' = rlc_connectorCentralFaceClosureEdges gamma gamma' \ rlc_connectorFourTraceEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceEdges_eq_sdiff gamma gamma'

/--
[rlc_connectorCentralFaceEdges_disjoint_fourTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceEdges_disjoint_fourTrace_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Disjoint (rlc_connectorCentralFaceEdges gamma gamma') (rlc_connectorFourTraceEdges gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceEdges_disjoint_fourTrace gamma gamma'

/--
[rlc_connectorCentralFaceEdge_endpoints_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceEdge_endpoints_mem_box_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
  {z : Site 2}
-- given
  (he : e ∈ rlc_connectorCentralFaceEdges gamma gamma')
  (hz : z ∈ e) :
-- imply
  z ∈ rlc_connectorBox n := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceEdge_endpoints_mem_box gamma gamma' he hz

/--
[rlc_connectorCentralFaceClosureEdge_endpoints_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceClosureEdge_endpoints_mem_box_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
  {z : Site 2}
-- given
  (he : e ∈ rlc_connectorCentralFaceClosureEdges gamma gamma')
  (hz : z ∈ e) :
-- imply
  z ∈ rlc_connectorBox n := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceClosureEdge_endpoints_mem_box gamma gamma' he hz

/--
[rlc_connectorCentralFacePlanarEdge_endpoints_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean)
-/
@[path]
private lemma rlc_connectorCentralFacePlanarEdge_endpoints_mem_box_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
  {z : Site 2}
-- given
  (he : e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma')
  (hz : z ∈ e) :
-- imply
  z ∈ rlc_connectorBox n := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFacePlanarEdge_endpoints_mem_box gamma gamma' he hz

/--
[RlcBookFaithfulTracePair.right_vertex_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean)
-/
@[path]
private lemma right_vertex_strict_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (h : RlcBookFaithfulTracePair gamma gamma')
  (hz : z ∈ rlc_pathVertices gamma.1)
  (hne : z ≠ (gamma.1.1 : Site 2)) :
-- imply
  0 < z 0 := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.right_vertex_strict h hz hne

/--
[RlcBookFaithfulTracePair.left_vertex_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean)
-/
@[path]
private lemma left_vertex_strict_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (h : RlcBookFaithfulTracePair gamma gamma')
  (hz : z ∈ rlc_pathVertices gamma'.1)
  (hne : z ≠ (gamma'.1.2.1 : Site 2)) :
-- imply
  z 0 < 0 := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.left_vertex_strict h hz hne

/--
[RlcBookFaithfulTracePair.axis_contacts_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean)
-/
@[path]
private lemma axis_contacts_strict_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (h : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  (gamma.1.1 : Site 2) 1 < (gamma'.1.2.1 : Site 2) 1 := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.axis_contacts_strict h

/--
[rlc_traceSplitCounterexample_bookPositioned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_bookPositioned_eq :
-- imply
  RlcBookPositionedTracePair rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_bookPositioned

/--
[rlc_scaleTwoDoubleFailure_not_bookPositioned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailure_not_bookPositioned_eq :
-- imply
  ¬ RlcBookPositionedTracePair rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailure_not_bookPositioned

/--
[rlc_scaleTwo_centralFace_mem_region](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean)
-/
@[path]
private lemma rlc_scaleTwo_centralFace_mem_region_eq :
-- imply
  rlc_connectorCentralFace ∈ rlc_connectorCentralFaceRegion rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft := by
-- proof
  apply StatMech.Universality.rlc_scaleTwo_centralFace_mem_region


-- created on 2026-10-23
