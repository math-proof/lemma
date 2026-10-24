import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceJordan
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_connectorCentralFace_faithfulDiscreteJordan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceJordan.lean)
-/
@[path]
private lemma rlc_connectorCentralFace_faithfulDiscreteJordan_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  whc_FaithfulDiscreteJordan (rlc_connectorCentralFacePlanarDomain gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFace_faithfulDiscreteJordan gamma gamma'

/--
[rlc_connectorCentralFaceReachSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceJordan.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceReachSet_finite_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  (rlc_connectorCentralFaceReachSet gamma gamma' rho).Finite := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceReachSet_finite gamma gamma' rho

/--
[rlc_connectorCentralFaceReachSet_extend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceJordan.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceReachSet_extend_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {v w : Site 2}
-- given
  (hv : v ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho)
  (hw : w ∈ rect (-2 * n) (2 * n) (-n) n)
  (hadj : (hypercubicLattice 2).Adj v w)
  (hopen : rlc_connectorCentralFaceAmbientConfig gamma gamma' rho s(v, w) = true) :
-- imply
  w ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceReachSet_extend gamma gamma' rho hv hw hadj hopen

/--
[rlc_connectorCentralFaceAmbientConfig_open_mem_planarEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceJordan.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceAmbientConfig_open_mem_planarEdges_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (Site 2)}
-- given
  (hopen : rlc_connectorCentralFaceAmbientConfig gamma gamma' rho e = true) :
-- imply
  e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceAmbientConfig_open_mem_planarEdges gamma gamma' rho hopen

/--
[rlc_openSub_centralFaceClosure_eq_openSubgraphInduce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceJordan.lean)
-/
@[path]
private lemma rlc_openSub_centralFaceClosure_eq_openSubgraphInduce_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.openSub (rlc_connectorCentralFaceClosureGraph gamma gamma') (rlc_connectorRestrictConfig (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho)) = openSubgraphInduce 2 (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho) (rect (-2 * n) (2 * n) (-n) n) := by
-- proof
  apply StatMech.Universality.rlc_openSub_centralFaceClosure_eq_openSubgraphInduce gamma gamma' rho

/--
[rlc_rightPathVertex_mem_centralFaceReachSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceJordan.lean)
-/
@[path]
private lemma rlc_rightPathVertex_mem_centralFaceReachSet_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_pathVertices gamma.1) :
-- imply
  z ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_rightPathVertex_mem_centralFaceReachSet gamma gamma' rho hz

/--
[rlc_leftPathVertex_not_mem_centralFaceReachSet_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceJordan.lean)
-/
@[path]
private lemma rlc_leftPathVertex_not_mem_centralFaceReachSet_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {z : Site 2}
-- given
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (hz : z ∈ rlc_pathVertices gamma'.1) :
-- imply
  z ∉ rlc_connectorCentralFaceReachSet gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_leftPathVertex_not_mem_centralFaceReachSet_of_failure gamma gamma' rho hno hz

/--
[rlc_centralFaceReachSet_axis_boundary_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceJordan.lean)
-/
@[path]
private lemma rlc_centralFaceReachSet_axis_boundary_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  ∃ p q : Site 2, (p, q) ∈ edgeBoundary 2 (rlc_connectorCentralFaceReachSet gamma gamma' rho) ∧ p ∈ rect (-2 * n) (2 * n) (-n) n ∧ q ∈ rect (-2 * n) (2 * n) (-n) n ∧ p 0 = 0 ∧ q 0 = 0 := by
-- proof
  apply StatMech.Universality.rlc_centralFaceReachSet_axis_boundary_of_failure gamma gamma' rho hno

/--
[rlc_centralFaceReachSet_verticalGap_boundary_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceJordan.lean)
-/
@[path]
private lemma rlc_centralFaceReachSet_verticalGap_boundary_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hposition : RlcBookPositionedTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  ∃ t : Int, (gamma.1.1 : Site 2) 1 ≤ t ∧ t < (gamma'.1.2.1 : Site 2) 1 ∧ ![0, t] ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho ∧ ![0, t + 1] ∉ rlc_connectorCentralFaceReachSet gamma gamma' rho ∧ ((![0, t], ![0, t + 1]) ∈ edgeBoundary 2 (rlc_connectorCentralFaceReachSet gamma gamma' rho)) := by
-- proof
  apply StatMech.Universality.rlc_centralFaceReachSet_verticalGap_boundary_of_failure gamma gamma' hposition rho hno

/--
[rlc_centralFaceReachSet_axis_anchored_boundaryCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceJordan.lean)
-/
@[path]
private lemma rlc_centralFaceReachSet_axis_anchored_boundaryCycle_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  ∃ (p q f g u : Site 2) (c : (faceBoundaryGraph (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Walk u u), (p, q) ∈ edgeBoundary 2 (rlc_connectorCentralFaceReachSet gamma gamma' rho) ∧ p ∈ rect (-2 * n) (2 * n) (-n) n ∧ q ∈ rect (-2 * n) (2 * n) (-n) n ∧ p 0 = 0 ∧ q 0 = 0 ∧ (faceBoundaryGraph (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Adj f g ∧ sharedPrimalEdge f g = s(p, q) ∧ c.IsCycle ∧ s(f, g) ∈ c.edges := by
-- proof
  apply StatMech.Universality.rlc_centralFaceReachSet_axis_anchored_boundaryCycle gamma gamma' rho hno

/--
[rlc_centralFaceReachSet_verticalGap_anchored_boundaryCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceJordan.lean)
-/
@[path]
private lemma rlc_centralFaceReachSet_verticalGap_anchored_boundaryCycle_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hposition : RlcBookPositionedTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  ∃ (t : Int) (f g u : Site 2) (c : (faceBoundaryGraph (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Walk u u), (gamma.1.1 : Site 2) 1 ≤ t ∧ t < (gamma'.1.2.1 : Site 2) 1 ∧ ![0, t] ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho ∧ ![0, t + 1] ∉ rlc_connectorCentralFaceReachSet gamma gamma' rho ∧ (faceBoundaryGraph (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Adj f g ∧ sharedPrimalEdge f g = s((![0, t] : Site 2), ![0, t + 1]) ∧ c.IsCycle ∧ s(f, g) ∈ c.edges := by
-- proof
  apply StatMech.Universality.rlc_centralFaceReachSet_verticalGap_anchored_boundaryCycle gamma gamma' hposition rho hno

/--
[rlc_centralFaceReachSet_verticalGap_complementaryArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceJordan.lean)
-/
@[path]
private lemma rlc_centralFaceReachSet_verticalGap_complementaryArc_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hposition : RlcBookPositionedTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  ∃ (t : Int) (f g : Site 2) (a : (faceBoundaryGraph (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Walk f g), (gamma.1.1 : Site 2) 1 ≤ t ∧ t < (gamma'.1.2.1 : Site 2) 1 ∧ ![0, t] ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho ∧ ![0, t + 1] ∉ rlc_connectorCentralFaceReachSet gamma gamma' rho ∧ (faceBoundaryGraph (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Adj f g ∧ sharedPrimalEdge f g = s((![0, t] : Site 2), ![0, t + 1]) ∧ s(f, g) ∉ a.edges := by
-- proof
  apply StatMech.Universality.rlc_centralFaceReachSet_verticalGap_complementaryArc gamma gamma' hposition rho hno

/--
[rlc_centralFaceContactSubwalk_edges_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceJordan.lean)
-/
@[path]
private lemma rlc_centralFaceContactSubwalk_edges_subset_eq
  {H : SimpleGraph (Site 2)}
  {f g x y : Site 2}
  {a : H.Walk f g}
-- given
  (hx : x ∈ a.support)
  (hy : y ∈ a.support) :
-- imply
  ∀ e ∈ (rlc_centralFaceContactSubwalk a hx hy).edges, e ∈ a.edges := by
-- proof
  apply StatMech.Universality.rlc_centralFaceContactSubwalk_edges_subset a hx hy

/--
[rlc_connectorCentralFaceReachSet_edgeBoundary_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceJordan.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceReachSet_edgeBoundary_closed_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {v w : Site 2}
-- given
  (hvw : (v, w) ∈ edgeBoundary 2 (rlc_connectorCentralFaceReachSet gamma gamma' rho)) :
-- imply
  rlc_connectorCentralFaceAmbientConfig gamma gamma' rho s(v, w) = false := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceReachSet_edgeBoundary_closed gamma gamma' rho hvw

/--
[rlc_connectorCentralFaceBoundary_le_openFaceDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceJordan.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceBoundary_le_openFaceDual_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  faceBoundaryGraph (rlc_connectorCentralFaceReachSet gamma gamma' rho) ≤ openSubgraph 2 (fci_faceDualConfig (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho)) := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceBoundary_le_openFaceDual gamma gamma' rho

/--
[rlc_boundaryContactArc_of_walkContactSegment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceJordan.lean)
-/
@[path]
private lemma rlc_boundaryContactArc_of_walkContactSegment_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {f g : Site 2}
  {a : (faceBoundaryGraph (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Walk f g}
-- given
  (hcontacts : RlcCentralFaceWalkContactSegment gamma gamma' rho a) :
-- imply
  RlcCentralFaceBoundaryContactArc gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_boundaryContactArc_of_walkContactSegment gamma gamma' rho a hcontacts

/--
[rlc_centralFacePIMS_openWalk_of_reflected_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceJordan.lean)
-/
@[path]
private lemma rlc_centralFacePIMS_openWalk_of_reflected_walk_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {x y : Site 2}
  {c : (openSubgraph 2 (rlc_dualReflectConfig (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho))).Walk x y}
-- given
  (hy : y ∈ rlc_pathVertices gamma'.1)
  (htarget : ∀ e ∈ c.edges, e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma') :
-- imply
  ∃ (hxBox : x ∈ rect (-2 * n) (2 * n) (-n) n) (hyBox : y ∈ rect (-2 * n) (2 * n) (-n) n), Nonempty ((FK.openSub (rlc_connectorCentralFaceClosureGraph gamma gamma') (rlc_connectorCentralFacePIMSConfig gamma gamma' rho)).Walk ⟨x, hxBox⟩ ⟨y, hyBox⟩) := by
-- proof
  apply StatMech.Universality.rlc_centralFacePIMS_openWalk_of_reflected_walk gamma gamma' rho c hy htarget

/--
[rlc_centralFacePIMS_success_of_boundaryContactArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceJordan.lean)
-/
@[path]
private lemma rlc_centralFacePIMS_success_of_boundaryContactArc_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (harc : RlcCentralFaceBoundaryContactArc gamma gamma' rho) :
-- imply
  rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈ rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_centralFacePIMS_success_of_boundaryContactArc gamma gamma' rho harc


-- created on 2026-10-23
