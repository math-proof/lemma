import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part43
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_twoChannelAmbientSourceEdge_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelAmbientSourceEdge_unique_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
  {f g : RlcTwoChannelAmbientSourceEdge gamma gamma' e} :
-- imply
  f = g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelAmbientSourceEdge_unique f g

/--
[rlc_twoChannelFullAmbientConfig_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullAmbientConfig_source_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {f : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet} :
-- imply
  rlc_twoChannelFullAmbientConfig gamma gamma' omega (f.1.map Subtype.val) = omega f := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullAmbientConfig_source gamma gamma' omega f

/--
[rlc_twoChannelFullAmbientConfig_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullAmbientConfig_trace_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
-- imply
  rlc_twoChannelFullAmbientConfig gamma gamma' omega e = true := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullAmbientConfig_trace gamma gamma' omega he

/--
[rlc_twoChannelFullDualConfig_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullDualConfig_apply_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {e : Sym2 (RlcConnectorVertex n)} :
-- imply
  rlc_twoChannelFullDualConfig gamma gamma' omega e = !(rlc_twoChannelFullAmbientConfig gamma gamma' omega (rlc_pimsEdgeEquiv (e.map Subtype.val))) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullDualConfig_apply gamma gamma' omega e

/--
[rlc_twoChannelFullDualConfig_of_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullDualConfig_of_source_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {e : Sym2 (RlcConnectorVertex n)}
  {f : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
-- given
  (hf : f.1.map Subtype.val = rlc_pimsEdgeEquiv (e.map Subtype.val)) :
-- imply
  rlc_twoChannelFullDualConfig gamma gamma' omega e = !(omega f) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullDualConfig_of_source gamma gamma' omega e f hf

/--
[rlc_twoChannelFullDualConfig_of_no_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullDualConfig_of_no_source_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {e : Sym2 (RlcConnectorVertex n)}
-- given
  (hsource : ¬Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma' (rlc_pimsEdgeEquiv (e.map Subtype.val)))) :
-- imply
  rlc_twoChannelFullDualConfig gamma gamma' omega e = if rlc_pimsEdgeEquiv (e.map Subtype.val) ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 then false else true := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullDualConfig_of_no_source gamma gamma' omega e hsource

/--
[rlc_twoChannelFullDualConfig_variable_eq_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullDualConfig_variable_eq_projection_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {e : RlcTwoChannelPIMSVariableTargetEdge gamma gamma'} :
-- imply
  rlc_twoChannelFullDualConfig gamma gamma' omega e.1 = rlc_twoChannelPIMSEdgeProjection gamma gamma' omega e.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullDualConfig_variable_eq_projection omega e

/--
[rlc_twoChannelFullAmbientConfig_embeddedEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullAmbientConfig_embeddedEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {f : Ising.kwg_Edge (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')} :
-- imply
  rlc_twoChannelFullAmbientConfig gamma gamma' omega (Ising.kwg_embeddedEdge (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') f) = rlc_connectorForceTraceConfig gamma gamma' (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) f.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullAmbientConfig_embeddedEdge gamma gamma' omega f

/--
[rlc_pimsEdgeEquiv_twoChannelReflectedDualEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_pimsEdgeEquiv_twoChannelReflectedDualEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f : Ising.kwg_Edge (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')} :
-- imply
  rlc_pimsEdgeEquiv (rlc_twoChannelReflectedDualEdge gamma gamma' f) = Ising.kwg_embeddedEdge (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') f := by
-- proof
  apply StatMech.Universality.rlc_pimsEdgeEquiv_twoChannelReflectedDualEdge gamma gamma' f

/--
[rlc_twoChannelFullAmbientDual_reflectedEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullAmbientDual_reflectedEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {f : Ising.kwg_Edge (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')} :
-- imply
  rlc_dualReflectConfig (rlc_twoChannelFullAmbientConfig gamma gamma' omega) (rlc_twoChannelReflectedDualEdge gamma gamma' f) = !(rlc_connectorForceTraceConfig gamma gamma' (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) f.1) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullAmbientDual_reflectedEdge gamma gamma' omega f

/--
[rlc_twoChannelFullAmbientDual_reflectedEdge_open_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullAmbientDual_reflectedEdge_open_iff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {f : Ising.kwg_Edge (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')} :
-- imply
  rlc_dualReflectConfig (rlc_twoChannelFullAmbientConfig gamma gamma' omega) (rlc_twoChannelReflectedDualEdge gamma gamma' f) = true ↔ f.1 ∉ (FK.openSub (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))).edgeSet := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullAmbientDual_reflectedEdge_open_iff gamma gamma' omega f

/--
[rlc_twoChannelFullAmbientConfig_open_mem_planarEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullAmbientConfig_open_mem_planarEdges_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {e : Sym2 (Site 2)}
-- given
  (hopen : rlc_twoChannelFullAmbientConfig gamma gamma' omega e = true) :
-- imply
  e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullAmbientConfig_open_mem_planarEdges gamma gamma' omega hopen

/--
[rlc_openSub_twoChannelAugmented_forceTrace_eq_fullAmbientInduce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_openSub_twoChannelAugmented_forceTrace_eq_fullAmbientInduce_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  FK.openSub (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)) = openSubgraphInduce 2 (rlc_twoChannelFullAmbientConfig gamma gamma' omega) (rect (-2 * n) (2 * n) (-n) n) := by
-- proof
  apply StatMech.Universality.rlc_openSub_twoChannelAugmented_forceTrace_eq_fullAmbientInduce gamma gamma' omega

/--
[rlc_twoChannelFullReachSet_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullReachSet_subset_box_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  rlc_twoChannelFullReachSet gamma gamma' omega ⊆ rect (-2 * n) (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullReachSet_subset_box gamma gamma' omega

/--
[rlc_twoChannelFullReachSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullReachSet_finite_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  (rlc_twoChannelFullReachSet gamma gamma' omega).Finite := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullReachSet_finite gamma gamma' omega

/--
[rlc_rightPathVertex_mem_twoChannelFullReachSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_rightPathVertex_mem_twoChannelFullReachSet_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_pathVertices gamma.1) :
-- imply
  z ∈ rlc_twoChannelFullReachSet gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_rightPathVertex_mem_twoChannelFullReachSet gamma gamma' omega hz

/--
[rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z : Site 2}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hz : z ∈ rlc_pathVertices gamma'.1) :
-- imply
  z ∉ rlc_twoChannelFullReachSet gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure gamma gamma' omega hno hz

/--
[rlc_twoChannelFullReachSet_extend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullReachSet_extend_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {v w : Site 2}
-- given
  (hv : v ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hw : w ∈ rect (-2 * n) (2 * n) (-n) n)
  (hadj : (hypercubicLattice 2).Adj v w)
  (hopen : rlc_twoChannelFullAmbientConfig gamma gamma' omega s(v, w) = true) :
-- imply
  w ∈ rlc_twoChannelFullReachSet gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullReachSet_extend gamma gamma' omega hv hw hadj hopen

/--
[rlc_twoChannelFullReachSet_edgeBoundary_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullReachSet_edgeBoundary_closed_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {v w : Site 2}
-- given
  (hvw : (v, w) ∈ edgeBoundary 2 (rlc_twoChannelFullReachSet gamma gamma' omega)) :
-- imply
  rlc_twoChannelFullAmbientConfig gamma gamma' omega s(v, w) = false := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullReachSet_edgeBoundary_closed gamma gamma' omega hvw

/--
[rlc_twoChannelFullBoundary_le_openFaceDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullBoundary_le_openFaceDual_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  faceBoundaryGraph (rlc_twoChannelFullReachSet gamma gamma' omega) ≤ openSubgraph 2 (fci_faceDualConfig (rlc_twoChannelFullAmbientConfig gamma gamma' omega)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullBoundary_le_openFaceDual gamma gamma' omega

/--
[rlc_twoChannelFullReachSet_edgeBoundary_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullReachSet_edgeBoundary_nonempty_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  (edgeBoundary 2 (rlc_twoChannelFullReachSet gamma gamma' omega)).Nonempty := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullReachSet_edgeBoundary_nonempty gamma gamma' omega

/--
[rlc_twoChannelFullReachSet_dualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullReachSet_dualCircuit_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  ∃ (u : Site 2) (c : (faceBoundaryGraph (rlc_twoChannelFullReachSet gamma gamma' omega)).Walk u u), c.IsCycle := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullReachSet_dualCircuit gamma gamma' omega

/--
[rlc_twoChannelFullReachSet_openFaceDualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullReachSet_openFaceDualCircuit_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  ∃ (u : Site 2) (c : (openSubgraph 2 (fci_faceDualConfig (rlc_twoChannelFullAmbientConfig gamma gamma' omega))).Walk u u), c.IsCycle := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullReachSet_openFaceDualCircuit gamma gamma' omega

/--
[rlc_twoChannelFullReachSet_reflectedOpenDualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullReachSet_reflectedOpenDualCircuit_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  ∃ (u : Site 2) (c : (openSubgraph 2 (rlc_dualReflectConfig (rlc_twoChannelFullAmbientConfig gamma gamma' omega))).Walk (rlc_dualReflect u) (rlc_dualReflect u)), c.IsCycle := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullReachSet_reflectedOpenDualCircuit gamma gamma' omega

/--
[rlc_twoChannelFullReachSet_axis_boundary_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullReachSet_axis_boundary_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
-- imply
  ∃ p q : Site 2, (p, q) ∈ edgeBoundary 2 (rlc_twoChannelFullReachSet gamma gamma' omega) ∧ p ∈ rect (-2 * n) (2 * n) (-n) n ∧ q ∈ rect (-2 * n) (2 * n) (-n) n ∧ p 0 = 0 ∧ q 0 = 0 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullReachSet_axis_boundary_of_failure gamma gamma' omega hno

/--
[rlc_twoChannelFullReachSet_axis_anchored_dualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullReachSet_axis_anchored_dualCircuit_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
-- imply
  ∃ (p q f g u : Site 2) (c : (faceBoundaryGraph (rlc_twoChannelFullReachSet gamma gamma' omega)).Walk u u), (p, q) ∈ edgeBoundary 2 (rlc_twoChannelFullReachSet gamma gamma' omega) ∧ p ∈ rect (-2 * n) (2 * n) (-n) n ∧ q ∈ rect (-2 * n) (2 * n) (-n) n ∧ p 0 = 0 ∧ q 0 = 0 ∧ (faceBoundaryGraph (rlc_twoChannelFullReachSet gamma gamma' omega)).Adj f g ∧ sharedPrimalEdge f g = s(p, q) ∧ c.IsCycle ∧ s(f, g) ∈ c.edges := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullReachSet_axis_anchored_dualCircuit gamma gamma' omega hno

/--
[rlc_twoChannelFullReachSet_openWalk_lift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullReachSet_openWalk_lift_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u v : RlcConnectorVertex n}
  {w : (openSubgraphInduce 2 (rlc_twoChannelFullAmbientConfig gamma gamma' omega) (rect (-2 * n) (2 * n) (-n) n)).Walk u v}
-- given
  (hu : (u : Site 2) ∈ rlc_twoChannelFullReachSet gamma gamma' omega) :
-- imply
  ∃ hv : (v : Site 2) ∈ rlc_twoChannelFullReachSet gamma gamma' omega, ((hypercubicLattice 2).induce (rlc_twoChannelFullReachSet gamma gamma' omega)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullReachSet_openWalk_lift gamma gamma' omega hu w

/--
[rlc_twoChannelFullReachSet_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullReachSet_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u v : Site 2}
-- given
  (hu : u ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hv : v ∈ rlc_twoChannelFullReachSet gamma gamma' omega) :
-- imply
  ((hypercubicLattice 2).induce (rlc_twoChannelFullReachSet gamma gamma' omega)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullReachSet_reachable gamma gamma' omega hu hv

/--
[rlc_twoChannelFullExteriorComponent_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullExteriorComponent_infinite_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  (rlc_twoChannelFullExteriorComponent gamma gamma' omega).supp.Infinite := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullExteriorComponent_infinite gamma gamma' omega

/--
[rlc_twoChannelFullReachSet_subset_filled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullReachSet_subset_filled_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  rlc_twoChannelFullReachSet gamma gamma' omega ⊆ rlc_twoChannelFullFilledReachSet gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega

/--
[rlc_twoChannelFullExteriorSet_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullExteriorSet_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u v : Site 2}
-- given
  (hu : u ∈ rlc_twoChannelFullExteriorSet gamma gamma' omega)
  (hv : v ∈ rlc_twoChannelFullExteriorSet gamma gamma' omega) :
-- imply
  ((hypercubicLattice 2).induce (rlc_twoChannelFullExteriorSet gamma gamma' omega)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullExteriorSet_reachable gamma gamma' omega hu hv

/--
[rlc_twoChannelFullFilledReachSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullFilledReachSet_finite_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  (rlc_twoChannelFullFilledReachSet gamma gamma' omega).Finite := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullFilledReachSet_finite gamma gamma' omega

/--
[rlc_twoChannelFullFilledReachSet_subset_connectorRect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullFilledReachSet_subset_connectorRect_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hn : 0 < n) :
-- imply
  rlc_twoChannelFullFilledReachSet gamma gamma' omega ⊆ rect (-2 * n) (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullFilledReachSet_subset_connectorRect hn gamma gamma' omega

/--
[rlc_twoChannelFullFilledReachSet_reaches_reachSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullFilledReachSet_reaches_reachSet_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u : Site 2}
-- given
  (hu : u ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
-- imply
  ∃ z : Site 2, ∃ hz : z ∈ rlc_twoChannelFullReachSet gamma gamma' omega, ((hypercubicLattice 2).induce (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Reachable ⟨u, hu⟩ ⟨z, rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega hz⟩ := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullFilledReachSet_reaches_reachSet gamma gamma' omega hu

/--
[rlc_twoChannelFullFilledReachSet_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullFilledReachSet_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u v : Site 2}
-- given
  (hu : u ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  (hv : v ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
-- imply
  ((hypercubicLattice 2).induce (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullFilledReachSet_reachable gamma gamma' omega hu hv

/--
[rlc_twoChannelFullFilledReachSet_reachable_in_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullFilledReachSet_reachable_in_barrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u v : Site 2}
-- given
  (hu : u ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  (hv : v ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
-- imply
  (latticeMinusBarrier (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Reachable u v := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullFilledReachSet_reachable_in_barrier gamma gamma' omega hu hv

/--
[rlc_twoChannelFullExteriorSet_reachable_in_filledBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullExteriorSet_reachable_in_filledBarrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u v : Site 2}
-- given
  (hu : u ∈ rlc_twoChannelFullExteriorSet gamma gamma' omega)
  (hv : v ∈ rlc_twoChannelFullExteriorSet gamma gamma' omega) :
-- imply
  (latticeMinusBarrier (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Reachable u v := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullExteriorSet_reachable_in_filledBarrier gamma gamma' omega hu hv

/--
[rlc_twoChannelFullFilledReachSet_faceBoundaryConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullFilledReachSet_faceBoundaryConnected_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  FaceBoundaryConnected (rlc_twoChannelFullFilledReachSet gamma gamma' omega) (phb_boundarySupport (rlc_twoChannelFullFilledReachSet gamma gamma' omega) (rlc_twoChannelFullFilledReachSet_finite gamma gamma' omega)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullFilledReachSet_faceBoundaryConnected gamma gamma' omega

/--
[rlc_twoChannelFullFilledBoundary_inside_mem_reachSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullFilledBoundary_inside_mem_reachSet_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {p q : Site 2}
-- given
  (hp : p ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  (hq : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  (hpq : (hypercubicLattice 2).Adj p q) :
-- imply
  p ∈ rlc_twoChannelFullReachSet gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullFilledBoundary_inside_mem_reachSet gamma gamma' omega hp hq hpq

/--
[rlc_twoChannelFullFilled_edgeBoundary_subset_reachSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullFilled_edgeBoundary_subset_reachSet_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {p q : Site 2}
-- given
  (hpq : (p, q) ∈ edgeBoundary 2 (rlc_twoChannelFullFilledReachSet gamma gamma' omega)) :
-- imply
  (p, q) ∈ edgeBoundary 2 (rlc_twoChannelFullReachSet gamma gamma' omega) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullFilled_edgeBoundary_subset_reachSet gamma gamma' omega hpq

/--
[rlc_twoChannelFullFilledFaceBoundaryGraph_le_reachFaceBoundaryGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullFilledFaceBoundaryGraph_le_reachFaceBoundaryGraph_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega) ≤ faceBoundaryGraph (rlc_twoChannelFullReachSet gamma gamma' omega) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullFilledFaceBoundaryGraph_le_reachFaceBoundaryGraph gamma gamma' omega

/--
[rlc_twoChannelFullFilledBoundary_le_openFaceDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullFilledBoundary_le_openFaceDual_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega) ≤ openSubgraph 2 (fci_faceDualConfig (rlc_twoChannelFullAmbientConfig gamma gamma' omega)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullFilledBoundary_le_openFaceDual gamma gamma' omega

/--
[rlc_leftPathVertex_mem_twoChannelFullExteriorSet_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_leftPathVertex_mem_twoChannelFullExteriorSet_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z : Site 2}
-- given
  (hposition : RlcBookPositionedTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hzPath : z ∈ rlc_pathVertices gamma'.1) :
-- imply
  z ∈ rlc_twoChannelFullExteriorSet gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_leftPathVertex_mem_twoChannelFullExteriorSet_of_failure gamma gamma' hposition omega hno hzPath

/--
[rlc_twoChannelFullFilledBoundaryContacts_of_faithful_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullFilledBoundaryContacts_of_faithful_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
-- imply
  RlcTwoChannelFullFilledBoundaryContacts gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullFilledBoundaryContacts_of_faithful_failure gamma gamma' hfaith omega hno

/--
[rlc_twoChannelFullFilledFaceBoundary_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullFilledFaceBoundary_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {f g : Site 2}
-- given
  (hf : f ∈ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
  (hg : g ∈ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support) :
-- imply
  (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Reachable f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullFilledFaceBoundary_reachable gamma gamma' omega hf hg

/--
[rlc_twoChannelFull_reflectedOpenDualWalk_of_faithful_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFull_reflectedOpenDualWalk_of_faithful_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
-- imply
  ∃ x y : Site 2, rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧ Nonempty ((openSubgraph 2 (rlc_dualReflectConfig (rlc_twoChannelFullAmbientConfig gamma gamma' omega))).Walk (rlc_dualReflect x) (rlc_dualReflect y)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFull_reflectedOpenDualWalk_of_faithful_failure gamma gamma' hfaith omega hno

/--
[rlc_openSub_twoChannelFullOuter_eq_induce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_openSub_twoChannelFullOuter_eq_induce_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  FK.openSub (rlc_twoChannelFullOuterGraph n) (rlc_twoChannelFullOuterConfig gamma gamma' omega) = openSubgraphInduce 2 (rlc_dualReflectConfig (rlc_twoChannelFullAmbientConfig gamma gamma' omega)) (rlc_twoChannelFullOuterBox n) := by
-- proof
  apply StatMech.Universality.rlc_openSub_twoChannelFullOuter_eq_induce gamma gamma' omega

/--
[rlc_dualReflect_faces_mem_fullOuterBox_of_shared_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_dualReflect_faces_mem_fullOuterBox_of_shared_endpoint_eq
  {n : Int}
  {f g x : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g)
  (hx : x ∈ sharedPrimalEdge f g)
  (hxRect : x ∈ rect (-2 * n) (2 * n) (-n) n) :
-- imply
  rlc_dualReflect f ∈ rlc_twoChannelFullOuterBox n ∧ rlc_dualReflect g ∈ rlc_twoChannelFullOuterBox n := by
-- proof
  apply StatMech.Universality.rlc_dualReflect_faces_mem_fullOuterBox_of_shared_endpoint hfg hx hxRect

/--
[rlc_twoChannelFullFilledBoundary_reflect_mem_outerBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullFilledBoundary_reflect_mem_outerBox_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {f g : Site 2}
-- given
  (hn : 0 < n)
  (hfg : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g) :
-- imply
  rlc_dualReflect f ∈ rlc_twoChannelFullOuterBox n ∧ rlc_dualReflect g ∈ rlc_twoChannelFullOuterBox n := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullFilledBoundary_reflect_mem_outerBox hn gamma gamma' omega hfg

/--
[rlc_twoChannelFullFilledBoundaryWalk_reflect_mem_outerBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullFilledBoundaryWalk_reflect_mem_outerBox_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y z : Site 2}
  {a : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk x y}
-- given
  (hn : 0 < n)
  (hy : y ∈ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
  (hz : z ∈ a.support) :
-- imply
  rlc_dualReflect z ∈ rlc_twoChannelFullOuterBox n := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullFilledBoundaryWalk_reflect_mem_outerBox hn gamma gamma' omega a hy hz

/--
[rlc_twoChannelFullOuter_success_of_faithful_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullOuter_success_of_faithful_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
-- imply
  rlc_twoChannelFullOuterConfig gamma gamma' omega ∈ rlc_twoChannelFullOuterConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullOuter_success_of_faithful_failure gamma gamma' hfaith omega hno

/--
[rlc_twoChannelReflectedDualEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelReflectedDualEdge_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Function.Injective (rlc_twoChannelReflectedDualEdge gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelReflectedDualEdge_injective gamma gamma'

/--
[rlc_openSub_twoChannelFullDual_eq_variable_sup_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_openSub_twoChannelFullDual_eq_variable_sup_exterior_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  FK.openSub (rlc_connectorTwoChannelGraph gamma gamma') (rlc_twoChannelFullDualConfig gamma gamma' omega) = FK.openSub (rlc_twoChannelFullVariableGraph gamma gamma') (rlc_twoChannelFullDualConfig gamma gamma' omega) ⊔ rlc_twoChannelFullExteriorGraph gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_openSub_twoChannelFullDual_eq_variable_sup_exterior gamma gamma' omega

/--
[rlc_twoChannelFullSourceEdge_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullSourceEdge_exists_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {target : RlcTwoChannelFullVariableTargetEdge gamma gamma'} :
-- imply
  ∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, source.1.map Subtype.val = rlc_pimsEdgeEquiv (target.1.map Subtype.val) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullSourceEdge_exists target

/--
[rlc_twoChannelFullSourceEdge_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullSourceEdge_map_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {target : RlcTwoChannelFullVariableTargetEdge gamma gamma'} :
-- imply
  (rlc_twoChannelFullSourceEdge target).1.map Subtype.val = rlc_pimsEdgeEquiv (target.1.map Subtype.val) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullSourceEdge_map target

/--
[rlc_twoChannelFullSourceEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullSourceEdge_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Function.Injective (rlc_twoChannelFullSourceEdge (gamma := gamma) (gamma' := gamma')) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullSourceEdge_injective

/--
[rlc_twoChannel_fullDualProjection_and_discardedBits_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannel_fullDualProjection_and_discardedBits_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Function.Injective (fun omega : RlcTwoChannelEdgeConfig gamma gamma' => ((fun e : RlcTwoChannelFullVariableTargetEdge gamma gamma' => rlc_twoChannelFullDualConfig gamma gamma' omega e.1), fun e : RlcTwoChannelFullDiscardedSourceEdge gamma gamma' => omega e.1)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_fullDualProjection_and_discardedBits_injective gamma gamma'

/--
[rlc_twoChannelFullDual_mem_event_iff_variableExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullDual_mem_event_iff_variableExterior_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  rlc_twoChannelFullDualConfig gamma gamma' omega ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma' ↔ rlc_twoChannelFullVariableProjection gamma gamma' omega ∈ rlc_twoChannelFullVariableExteriorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullDual_mem_event_iff_variableExterior gamma gamma' omega

/--
[rlc_twoChannelIndexedOuterTarget_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedOuterTarget_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Function.Injective (rlc_twoChannelIndexedOuterTarget gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedOuterTarget_injective gamma gamma'

/--
[rlc_twoChannelIndexedAugmentedEdge_reflected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedAugmentedEdge_reflected_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {target : RlcTwoChannelFullVariableTargetEdge gamma gamma'} :
-- imply
  rlc_twoChannelReflectedDualEdge gamma gamma' (rlc_twoChannelIndexedAugmentedEdge target) = target.1.map Subtype.val := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedAugmentedEdge_reflected target

/--
[rlc_twoChannelIndexedOuterEdge_variable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedOuterEdge_variable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {target : RlcTwoChannelFullVariableTargetEdge gamma gamma'} :
-- imply
  rlc_twoChannelIndexedOuterEdge gamma gamma' (rlc_twoChannelIndexedAugmentedEdge target) = target.1.map (rlc_twoChannelIndexedOuterTarget gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedOuterEdge_variable target

/--
[rlc_twoChannelIndexedOuterEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedOuterEdge_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Function.Injective (rlc_twoChannelIndexedOuterEdge gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedOuterEdge_injective gamma gamma'

/--
[rlc_twoChannelIndexedFaceProjection_outerEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedFaceProjection_outerEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f : Ising.kwg_Edge (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')} :
-- imply
  (rlc_twoChannelIndexedOuterEdge gamma gamma' f).map (rlc_twoChannelIndexedFaceProjection gamma gamma') = Ising.kwg_dualEnds (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') f := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedFaceProjection_outerEdge gamma gamma' f

/--
[rlc_twoChannelIndexedFaceProjection_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedFaceProjection_face_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {C : Ising.kwg_Face (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')} :
-- imply
  rlc_twoChannelIndexedFaceProjection gamma gamma' (rlc_twoChannelIndexedOuterFace gamma gamma' C) = C := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedFaceProjection_face gamma gamma' C

/--
[rlc_twoChannelIndexedSpoke_adj_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedSpoke_adj_face_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x : RlcTwoChannelIndexedOuterVertex gamma gamma'}
-- given
  (hx : ¬RlcTwoChannelIndexedIsFace gamma gamma' x) :
-- imply
  (rlc_twoChannelIndexedSpokeGraph gamma gamma').Adj x (rlc_twoChannelIndexedOuterFace gamma gamma' (rlc_twoChannelIndexedFaceProjection gamma gamma' x)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedSpoke_adj_face gamma gamma' x hx

/--
[rlc_twoChannelIndexedFaceProjection_eq_of_spoke](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedFaceProjection_eq_of_spoke_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y : RlcTwoChannelIndexedOuterVertex gamma gamma'}
-- given
  (hxy : (rlc_twoChannelIndexedSpokeGraph gamma gamma').Adj x y) :
-- imply
  rlc_twoChannelIndexedFaceProjection gamma gamma' x = rlc_twoChannelIndexedFaceProjection gamma gamma' y := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedFaceProjection_eq_of_spoke gamma gamma' hxy

/--
[rlc_twoChannelIndexedOuterConfig_randomEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedOuterConfig_randomEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {f : Ising.kwg_Edge (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')} :
-- imply
  rlc_twoChannelIndexedOuterConfig gamma gamma' omega (rlc_twoChannelIndexedOuterEdge gamma gamma' f) = !(rlc_connectorForceTraceConfig gamma gamma' (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) f.1) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedOuterConfig_randomEdge gamma gamma' omega f

/--
[rlc_twoChannelIndexedFaceTag_eq_true_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedFaceTag_eq_true_iff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x : RlcTwoChannelIndexedOuterVertex gamma gamma'} :
-- imply
  rlc_twoChannelIndexedFaceTag gamma gamma' x = true ↔ RlcTwoChannelIndexedIsFace gamma gamma' x := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedFaceTag_eq_true_iff gamma gamma' x

/--
[rlc_twoChannelIndexedFaceTag_outerEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedFaceTag_outerEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f : Ising.kwg_Edge (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')} :
-- imply
  (rlc_twoChannelIndexedOuterEdge gamma gamma' f).map (rlc_twoChannelIndexedFaceTag gamma gamma') = s(false, false) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedFaceTag_outerEdge gamma gamma' f

/--
[rlc_twoChannelIndexedSpoke_faceTag_ne_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedSpoke_faceTag_ne_false_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y : RlcTwoChannelIndexedOuterVertex gamma gamma'}
-- given
  (hxy : (rlc_twoChannelIndexedSpokeGraph gamma gamma').Adj x y) :
-- imply
  s(x, y).map (rlc_twoChannelIndexedFaceTag gamma gamma') ≠ s(false, false) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedSpoke_faceTag_ne_false gamma gamma' hxy

/--
[rlc_twoChannelIndexedOuterEdge_not_mem_spoke](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedOuterEdge_not_mem_spoke_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f : Ising.kwg_Edge (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')} :
-- imply
  rlc_twoChannelIndexedOuterEdge gamma gamma' f ∉ (rlc_twoChannelIndexedSpokeGraph gamma gamma').edgeSet := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedOuterEdge_not_mem_spoke gamma gamma' f

/--
[rlc_twoChannelIndexedOuterConfig_spoke](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedOuterConfig_spoke_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {e : Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma')}
-- given
  (he : e ∈ (rlc_twoChannelIndexedSpokeGraph gamma gamma').edgeSet) :
-- imply
  rlc_twoChannelIndexedOuterConfig gamma gamma' omega e = true := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedOuterConfig_spoke gamma gamma' omega he

/--
[rlc_twoChannelIndexedOuterEdge_ne_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedOuterEdge_ne_diag_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f : Ising.kwg_Edge (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')}
  {x : RlcTwoChannelIndexedOuterVertex gamma gamma'} :
-- imply
  rlc_twoChannelIndexedOuterEdge gamma gamma' f ≠ s(x, x) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedOuterEdge_ne_diag gamma gamma' f x

/--
[rlc_twoChannelIndexedOuterEdge_mem_random](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedOuterEdge_mem_random_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f : Ising.kwg_Edge (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')} :
-- imply
  rlc_twoChannelIndexedOuterEdge gamma gamma' f ∈ (rlc_twoChannelIndexedRandomGraph gamma gamma').edgeSet := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedOuterEdge_mem_random gamma gamma' f

/--
[rlc_twoChannelIndexedSpoke_le_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedSpoke_le_open_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  rlc_twoChannelIndexedSpokeGraph gamma gamma' ≤ rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedSpoke_le_open gamma gamma' omega

/--
[rlc_twoChannelIndexedOuterEdge_open_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedOuterEdge_open_iff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {f : Ising.kwg_Edge (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')} :
-- imply
  rlc_twoChannelIndexedOuterEdge gamma gamma' f ∈ (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).edgeSet ↔ f.1 ∉ (FK.openSub (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))).edgeSet := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedOuterEdge_open_iff gamma gamma' omega f

/--
[rlc_twoChannelIndexedOuterEdge_endpoints_not_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedOuterEdge_endpoints_not_face_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f : Ising.kwg_Edge (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')}
  {x y : RlcTwoChannelIndexedOuterVertex gamma gamma'}
-- given
  (hxy : rlc_twoChannelIndexedOuterEdge gamma gamma' f = s(x, y)) :
-- imply
  ¬RlcTwoChannelIndexedIsFace gamma gamma' x ∧ ¬RlcTwoChannelIndexedIsFace gamma gamma' y := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedOuterEdge_endpoints_not_face gamma gamma' f hxy

/--
[rlc_twoChannelIndexedFaceProjection_reachable_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedFaceProjection_reachable_of_adj_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y : RlcTwoChannelIndexedOuterVertex gamma gamma'}
-- given
  (hxy : (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Adj x y) :
-- imply
  (BeffaraDC.pfdClosedDual (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') (FK.openSub (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))).Reachable (rlc_twoChannelIndexedFaceProjection gamma gamma' x) (rlc_twoChannelIndexedFaceProjection gamma gamma' y) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedFaceProjection_reachable_of_adj gamma gamma' omega hxy

/--
[rlc_twoChannelIndexedFaceProjection_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedFaceProjection_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y : RlcTwoChannelIndexedOuterVertex gamma gamma'}
-- given
  (hxy : (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Reachable x y) :
-- imply
  (BeffaraDC.pfdClosedDual (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') (FK.openSub (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))).Reachable (rlc_twoChannelIndexedFaceProjection gamma gamma' x) (rlc_twoChannelIndexedFaceProjection gamma gamma' y) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedFaceProjection_reachable gamma gamma' omega hxy

/--
[rlc_twoChannelIndexedFace_reachable_of_pfd_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedFace_reachable_of_pfd_adj_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {C D : Ising.kwg_Face (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')}
-- given
  (hCD : (BeffaraDC.pfdClosedDual (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') (FK.openSub (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))).Adj C D) :
-- imply
  (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Reachable (rlc_twoChannelIndexedOuterFace gamma gamma' C) (rlc_twoChannelIndexedOuterFace gamma gamma' D) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedFace_reachable_of_pfd_adj gamma gamma' omega hCD

/--
[rlc_twoChannelIndexedFace_reachable_of_pfd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedFace_reachable_of_pfd_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {C D : Ising.kwg_Face (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')}
-- given
  (hCD : (BeffaraDC.pfdClosedDual (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') (FK.openSub (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))).Reachable C D) :
-- imply
  (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Reachable (rlc_twoChannelIndexedOuterFace gamma gamma' C) (rlc_twoChannelIndexedOuterFace gamma gamma' D) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedFace_reachable_of_pfd gamma gamma' omega hCD

/--
[rlc_twoChannelIndexedOuter_reachable_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedOuter_reachable_face_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x : RlcTwoChannelIndexedOuterVertex gamma gamma'} :
-- imply
  (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Reachable x (rlc_twoChannelIndexedOuterFace gamma gamma' (rlc_twoChannelIndexedFaceProjection gamma gamma' x)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedOuter_reachable_face gamma gamma' omega x

/--
[rlc_twoChannelIndexedOuter_reachable_iff_pfd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedOuter_reachable_iff_pfd_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y : RlcTwoChannelIndexedOuterVertex gamma gamma'} :
-- imply
  (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Reachable x y ↔ (BeffaraDC.pfdClosedDual (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') (FK.openSub (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))).Reachable (rlc_twoChannelIndexedFaceProjection gamma gamma' x) (rlc_twoChannelIndexedFaceProjection gamma gamma' y) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedOuter_reachable_iff_pfd gamma gamma' omega x y

/--
[rlc_twoChannelIndexedOuterTargets_reachable_of_pfd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedOuterTargets_reachable_of_pfd_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y : RlcConnectorVertex n}
-- given
  (hxy : (BeffaraDC.pfdClosedDual (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') (FK.openSub (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))).Reachable (BeffaraDC.pfdFace (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') (rlc_dualReflect.symm x.1)) (BeffaraDC.pfdFace (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') (rlc_dualReflect.symm y.1))) :
-- imply
  (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Reachable (rlc_twoChannelIndexedOuterTarget gamma gamma' x) (rlc_twoChannelIndexedOuterTarget gamma gamma' y) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedOuterTargets_reachable_of_pfd gamma gamma' omega x y hxy

/--
[rlc_twoChannelIndexedOuterConfig_closedSource_randomEdge_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedOuterConfig_closedSource_randomEdge_iff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f : Ising.kwg_Edge (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')} :
-- imply
  rlc_twoChannelIndexedOuterConfig gamma gamma' (fun _ => false) (rlc_twoChannelIndexedOuterEdge gamma gamma' f) = true ↔ f.1 ∉ (rlc_connectorTraceWiring gamma gamma').edgeSet := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedOuterConfig_closedSource_randomEdge_iff gamma gamma' f

/--
[rlc_twoChannelIndexedOuterConfig_variable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedOuterConfig_variable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {target : RlcTwoChannelFullVariableTargetEdge gamma gamma'} :
-- imply
  rlc_twoChannelIndexedOuterConfig gamma gamma' omega (target.1.map (rlc_twoChannelIndexedOuterTarget gamma gamma')) = rlc_twoChannelFullDualConfig gamma gamma' omega target.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedOuterConfig_variable gamma gamma' omega target

/--
[rlc_twoChannelIndexedRandomGraph_adj_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedRandomGraph_adj_target_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y : RlcConnectorVertex n} :
-- imply
  (rlc_twoChannelIndexedRandomGraph gamma gamma').Adj (rlc_twoChannelIndexedOuterTarget gamma gamma' x) (rlc_twoChannelIndexedOuterTarget gamma gamma' y) ↔ (rlc_twoChannelFullVariableGraph gamma gamma').Adj x y := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedRandomGraph_adj_target gamma gamma' x y

/--
[rlc_twoChannelIndexedSpokeGraph_not_adj_targets](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedSpokeGraph_not_adj_targets_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y : RlcConnectorVertex n} :
-- imply
  ¬(rlc_twoChannelIndexedSpokeGraph gamma gamma').Adj (rlc_twoChannelIndexedOuterTarget gamma gamma' x) (rlc_twoChannelIndexedOuterTarget gamma gamma' y) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedSpokeGraph_not_adj_targets gamma gamma' x y

/--
[rlc_twoChannelIndexedOuter_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedOuter_adjMatch_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  FK.ocd_AdjMatch (rlc_twoChannelFullVariableGraph gamma gamma') (rlc_twoChannelIndexedOuterGraph gamma gamma') (rlc_twoChannelIndexedOuterTarget gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedOuter_adjMatch gamma gamma'

/--
[rlc_twoChannelIndexed_condProb_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexed_condProb_eq_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {psi : ConfigSpace (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma'))}
  {eta : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  FK.condBcProb (rlc_twoChannelIndexedOuterGraph gamma gamma') (Lattice.boundaryCliqueGraph (fun _ => False)) p q (FK.ocd_innerEdgeFinset (rlc_twoChannelIndexedOuterTarget gamma gamma')) psi (FK.ocd_psiExt (rlc_twoChannelIndexedOuterTarget gamma gamma') psi eta) = FK.bcProb (rlc_twoChannelFullVariableGraph gamma gamma') (FK.ocd_inducedWiring (rlc_twoChannelIndexedOuterGraph gamma gamma') (rlc_twoChannelIndexedOuterTarget gamma gamma') (fun _ => False) psi) p q eta := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexed_condProb_eq gamma gamma' hp hp1 hq psi eta

/--
[rlc_twoChannelFullVariableTargetEdge_inner_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullVariableTargetEdge_inner_exists_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {target : RlcTwoChannelFullVariableTargetEdge gamma gamma'} :
-- imply
  ∃ e : (rlc_twoChannelFullInnerGraph gamma gamma').edgeSet, e.1.map Subtype.val = target.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullVariableTargetEdge_inner_exists target

/--
[rlc_twoChannelFullVariableTargetEdge_inner_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullVariableTargetEdge_inner_map_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {target : RlcTwoChannelFullVariableTargetEdge gamma gamma'} :
-- imply
  (rlc_twoChannelFullVariableTargetEdge_inner target).1.map Subtype.val = target.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullVariableTargetEdge_inner_map target

/--
[rlc_twoChannelFullInnerOuterVertex_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullInnerOuterVertex_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Function.Injective (rlc_twoChannelFullInnerOuterVertex gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullInnerOuterVertex_injective gamma gamma'

/--
[rlc_twoChannelFullInnerOuter_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullInnerOuter_adjMatch_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  FK.ocd_AdjMatch (rlc_twoChannelFullInnerGraph gamma gamma') (rlc_twoChannelIndexedOuterGraph gamma gamma') (rlc_twoChannelFullInnerOuterVertex gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullInnerOuter_adjMatch gamma gamma'

/--
[rlc_twoChannelIndexedOuterEdge_mem_innerRange_of_retained](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedOuterEdge_mem_innerRange_of_retained_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f : Ising.kwg_Edge (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')}
-- given
  (hret : RlcTwoChannelIndexedRetainedEdge gamma gamma' f) :
-- imply
  rlc_twoChannelIndexedOuterEdge gamma gamma' f ∈ Set.range (FK.ocd_innerEdge (rlc_twoChannelFullInnerOuterVertex gamma gamma')) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedOuterEdge_mem_innerRange_of_retained gamma gamma' f hret

/--
[rlc_twoChannelIndexedOuterEdge_variable_mem_innerRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedOuterEdge_variable_mem_innerRange_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {target : RlcTwoChannelFullVariableTargetEdge gamma gamma'} :
-- imply
  rlc_twoChannelIndexedOuterEdge gamma gamma' (rlc_twoChannelIndexedAugmentedEdge target) ∈ Set.range (FK.ocd_innerEdge (rlc_twoChannelFullInnerOuterVertex gamma gamma')) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedOuterEdge_variable_mem_innerRange target

/--
[rlc_twoChannelFullIndexed_innerActive_eq_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullIndexed_innerActive_eq_projection_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  FK.restrictActive (rlc_twoChannelFullInnerGraph gamma gamma') (FK.ocd_innerRestrict (rlc_twoChannelFullInnerOuterVertex gamma gamma') (rlc_twoChannelIndexedOuterConfig gamma gamma' omega)) = rlc_twoChannelFullInnerActiveProjection gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullIndexed_innerActive_eq_projection gamma gamma' omega

/--
[rlc_twoChannelFullInnerToVariable_innerRestrict_eq_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullInnerToVariable_innerRestrict_eq_projection_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  rlc_twoChannelFullInnerToVariable gamma gamma' (FK.ocd_innerRestrict (rlc_twoChannelFullInnerOuterVertex gamma gamma') (rlc_twoChannelIndexedOuterConfig gamma gamma' omega)) = rlc_twoChannelFullVariableProjection gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullInnerToVariable_innerRestrict_eq_projection gamma gamma' omega

/--
[rlc_twoChannelFullVariableExteriorEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullVariableExteriorEvent_isIncreasing_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  IsIncreasing (rlc_twoChannelFullVariableExteriorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullVariableExteriorEvent_isIncreasing gamma gamma'

/--
[rlc_twoChannelFullInnerExteriorEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullInnerExteriorEvent_isIncreasing_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  IsIncreasing (rlc_twoChannelFullInnerExteriorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullInnerExteriorEvent_isIncreasing gamma gamma'

/--
[rlc_twoChannelFullIndexed_innerExteriorEvent_iff_fullDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullIndexed_innerExteriorEvent_iff_fullDual_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  FK.ocd_innerRestrict (rlc_twoChannelFullInnerOuterVertex gamma gamma') (rlc_twoChannelIndexedOuterConfig gamma gamma' omega) ∈ rlc_twoChannelFullInnerExteriorEvent gamma gamma' ↔ rlc_twoChannelFullDualConfig gamma gamma' omega ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullIndexed_innerExteriorEvent_iff_fullDual gamma gamma' omega

/--
[rlc_twoChannelIndexedOuterConfig_agreesOff_of_discarded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedOuterConfig_agreesOff_of_discarded_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega omega' : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hdiscarded : ∀ e : RlcTwoChannelFullDiscardedSourceEdge gamma gamma', omega e.1 = omega' e.1) :
-- imply
  FK.AgreesOff (FK.ocd_innerEdgeFinset (rlc_twoChannelFullInnerOuterVertex gamma gamma')) (rlc_twoChannelIndexedOuterConfig gamma gamma' omega) (rlc_twoChannelIndexedOuterConfig gamma gamma' omega') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedOuterConfig_agreesOff_of_discarded gamma gamma' omega omega' hdiscarded

/--
[rlc_twoChannelFullIndexedOuterState_supported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullIndexedOuterState_supported_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  RlcTwoChannelFullIndexedFibreSupported gamma gamma' (rlc_twoChannelFullIndexedOuterState gamma gamma' omega) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullIndexedOuterState_supported gamma gamma' omega

/--
[rlc_twoChannelFullIndexedOuterState_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullIndexedOuterState_fixed_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  FK.ocd_outProj (rlc_twoChannelFullInnerOuterVertex gamma gamma') (rlc_twoChannelFullIndexedOuterState gamma gamma' omega) = rlc_twoChannelFullIndexedOuterState gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullIndexedOuterState_fixed gamma gamma' omega

/--
[rlc_twoChannelFullIndexedOuterState_eq_of_discarded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullIndexedOuterState_eq_of_discarded_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega omega' : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hdiscarded : ∀ e : RlcTwoChannelFullDiscardedSourceEdge gamma gamma', omega e.1 = omega' e.1) :
-- imply
  rlc_twoChannelFullIndexedOuterState gamma gamma' omega = rlc_twoChannelFullIndexedOuterState gamma gamma' omega' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullIndexedOuterState_eq_of_discarded gamma gamma' omega omega' hdiscarded

/--
[rlc_twoChannelIndexedOuterConfig_le_closedSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedOuterConfig_le_closedSource_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  rlc_twoChannelIndexedOuterConfig gamma gamma' omega ≤ rlc_twoChannelIndexedOuterConfig gamma gamma' (fun _ => false) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedOuterConfig_le_closedSource gamma gamma' omega

/--
[rlc_twoChannelFullIndexedOuterState_le_max](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullIndexedOuterState_le_max_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  rlc_twoChannelFullIndexedOuterState gamma gamma' omega ≤ rlc_twoChannelFullIndexedOuterMaxState gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullIndexedOuterState_le_max gamma gamma' omega

/--
[rlc_twoChannelFullIndexedOuterState_reconstruct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullIndexedOuterState_reconstruct_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  FK.ocd_psiExt (rlc_twoChannelFullInnerOuterVertex gamma gamma') (rlc_twoChannelFullIndexedOuterState gamma gamma' omega) (FK.ocd_innerRestrict (rlc_twoChannelFullInnerOuterVertex gamma gamma') (rlc_twoChannelIndexedOuterConfig gamma gamma' omega)) = rlc_twoChannelIndexedOuterConfig gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullIndexedOuterState_reconstruct gamma gamma' omega

/--
[rlc_twoChannelFullInnerInducedWiring_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullInnerInducedWiring_mono_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {psi phi : ConfigSpace (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma'))}
-- given
  (hpsi : psi ≤ phi) :
-- imply
  rlc_twoChannelFullInnerInducedWiring gamma gamma' psi ≤ rlc_twoChannelFullInnerInducedWiring gamma gamma' phi := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullInnerInducedWiring_mono gamma gamma' hpsi

/--
[rlc_twoChannelFullInnerInducedWiring_le_maxSupported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullInnerInducedWiring_le_maxSupported_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  rlc_twoChannelFullInnerInducedWiring gamma gamma' (rlc_twoChannelFullIndexedOuterState gamma gamma' omega) ≤ rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullInnerInducedWiring_le_maxSupported gamma gamma' omega

/--
[rlc_twoChannelFullMaxOuterContraction_eq_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullMaxOuterContraction_eq_of_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y : RlcTwoChannelIndexedOuterVertex gamma gamma'}
-- given
  (hxy : (rlc_twoChannelFullMaxOutsideGraph gamma gamma').Reachable x y) :
-- imply
  rlc_twoChannelFullMaxOuterContraction gamma gamma' x = rlc_twoChannelFullMaxOuterContraction gamma gamma' y := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullMaxOuterContraction_eq_of_reachable gamma gamma' hxy

/--
[rlc_twoChannelFullMaxInnerContraction_eq_of_maxWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullMaxInnerContraction_eq_of_maxWiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y : RlcTwoChannelFullInnerVertex gamma gamma'}
-- given
  (hxy : (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma').Adj x y) :
-- imply
  rlc_twoChannelFullMaxInnerContraction gamma gamma' x = rlc_twoChannelFullMaxInnerContraction gamma gamma' y := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullMaxInnerContraction_eq_of_maxWiring gamma gamma' hxy

/--
[rlc_twoChannelFullMaxComponentTraceRep_onEither](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullMaxComponentTraceRep_onEither_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {C : RlcTwoChannelFullMaxOutsideComponent gamma gamma'} :
-- imply
  rlc_connectorOnEither gamma gamma' (rlc_twoChannelFullMaxComponentTraceRep gamma gamma' C) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullMaxComponentTraceRep_onEither gamma gamma' C

/--
[rlc_twoChannelFullMaxComponentTraceRep_eq_or_mergedClique_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullMaxComponentTraceRep_eq_or_mergedClique_adj_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {C D : RlcTwoChannelFullMaxOutsideComponent gamma gamma'} :
-- imply
  rlc_twoChannelFullMaxComponentTraceRep gamma gamma' C = rlc_twoChannelFullMaxComponentTraceRep gamma gamma' D ∨ (rlc_connectorMergedClique gamma gamma').Adj (rlc_twoChannelFullMaxComponentTraceRep gamma gamma' C) (rlc_twoChannelFullMaxComponentTraceRep gamma gamma' D) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullMaxComponentTraceRep_eq_or_mergedClique_adj gamma gamma' C D

/--
[rlc_twoChannelFullMaxWiring_traceRep_eq_or_mergedClique_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullMaxWiring_traceRep_eq_or_mergedClique_adj_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y : RlcTwoChannelFullInnerVertex gamma gamma'}
-- given
  (hxy : (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma').Adj x y) :
-- imply
  rlc_twoChannelFullMaxComponentTraceRep gamma gamma' (rlc_twoChannelFullMaxInnerContraction gamma gamma' x) = rlc_twoChannelFullMaxComponentTraceRep gamma gamma' (rlc_twoChannelFullMaxInnerContraction gamma gamma' y) ∨ (rlc_connectorMergedClique gamma gamma').Adj (rlc_twoChannelFullMaxComponentTraceRep gamma gamma' (rlc_twoChannelFullMaxInnerContraction gamma gamma' x)) (rlc_twoChannelFullMaxComponentTraceRep gamma gamma' (rlc_twoChannelFullMaxInnerContraction gamma gamma' y)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullMaxWiring_traceRep_eq_or_mergedClique_adj gamma gamma' hxy

/--
[rlc_twoChannelFullMaxInnerTraceRep_onEither](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullMaxInnerTraceRep_onEither_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x : RlcTwoChannelFullInnerVertex gamma gamma'} :
-- imply
  rlc_connectorOnEither gamma gamma' (rlc_twoChannelFullMaxInnerTraceRep gamma gamma' x) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullMaxInnerTraceRep_onEither gamma gamma' x

/--
[rlc_twoChannelFullMaxInnerContraction_eq_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullMaxInnerContraction_eq_of_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y : RlcTwoChannelFullInnerVertex gamma gamma'}
-- given
  (hxy : (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma').Reachable x y) :
-- imply
  rlc_twoChannelFullMaxInnerContraction gamma gamma' x = rlc_twoChannelFullMaxInnerContraction gamma gamma' y := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullMaxInnerContraction_eq_of_reachable gamma gamma' hxy

/--
[rlc_twoChannelFullMaxInnerTraceRep_eq_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullMaxInnerTraceRep_eq_of_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y : RlcTwoChannelFullInnerVertex gamma gamma'}
-- given
  (hxy : (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma').Reachable x y) :
-- imply
  rlc_twoChannelFullMaxInnerTraceRep gamma gamma' x = rlc_twoChannelFullMaxInnerTraceRep gamma gamma' y := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullMaxInnerTraceRep_eq_of_reachable gamma gamma' hxy

/--
[rlc_twoChannelFullInnerMaxSupportedWiring_le_traceKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullInnerMaxSupportedWiring_le_traceKernel_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma' ≤ rlc_twoChannelFullMaxTraceKernelWiring gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullInnerMaxSupportedWiring_le_traceKernel gamma gamma'

/--
[rlc_twoChannelFullIndexed_innerEvent_eq_induced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullIndexed_innerEvent_eq_induced_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {psi : ConfigSpace (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma'))}
  {A : Set (ConfigSpace (Sym2 (RlcTwoChannelFullInnerVertex gamma gamma')))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (∑ rho, (FK.ocd_innerRestrict (rlc_twoChannelFullInnerOuterVertex gamma gamma') ⁻¹' A).indicator (fun _ => (1 : Real)) rho * FK.condBcProb (rlc_twoChannelIndexedOuterGraph gamma gamma') (Lattice.boundaryCliqueGraph (fun _ => False)) p q (FK.ocd_innerEdgeFinset (rlc_twoChannelFullInnerOuterVertex gamma gamma')) psi rho) = ∑ eta, A.indicator (fun _ => (1 : Real)) eta * FK.bcProb (rlc_twoChannelFullInnerGraph gamma gamma') (rlc_twoChannelFullInnerInducedWiring gamma gamma' psi) p q eta := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullIndexed_innerEvent_eq_induced gamma gamma' hp hp1 hq psi A

/--
[rlc_twoChannelFullIndexed_actualInnerEvent_le_maxSupported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullIndexed_actualInnerEvent_le_maxSupported_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {A : Set (ConfigSpace (Sym2 (RlcTwoChannelFullInnerVertex gamma gamma')))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ rho, (FK.ocd_innerRestrict (rlc_twoChannelFullInnerOuterVertex gamma gamma') ⁻¹' A).indicator (fun _ => (1 : Real)) rho * FK.condBcProb (rlc_twoChannelIndexedOuterGraph gamma gamma') (Lattice.boundaryCliqueGraph (fun _ => False)) p q (FK.ocd_innerEdgeFinset (rlc_twoChannelFullInnerOuterVertex gamma gamma')) (rlc_twoChannelFullIndexedOuterState gamma gamma' omega) rho) ≤ FK.bcEventMass (rlc_twoChannelFullInnerGraph gamma gamma') (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma') p q A := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullIndexed_actualInnerEvent_le_maxSupported gamma gamma' hp hp1 hq omega A hA

/--
[rlc_twoChannelFullIndexed_actualConnectorFibreMass_le_maxSupported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullIndexed_actualConnectorFibreMass_le_maxSupported_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  rlc_twoChannelFullIndexed_actualConnectorFibreMass gamma gamma' p q omega ≤ FK.bcEventMass (rlc_twoChannelFullInnerGraph gamma gamma') (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma') p q (rlc_twoChannelFullInnerExteriorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullIndexed_actualConnectorFibreMass_le_maxSupported gamma gamma' hp hp1 hq omega

/--
[rlc_twoChannelFullIndexed_actualConnectorMixture_le_maxSupported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullIndexed_actualConnectorMixture_le_maxSupported_eq
  {n : Int}
  [Fintype I]
  [DecidableEq I]
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {weight : I → Real}
  {omega : I → RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hweight : ∀ i, 0 ≤ weight i)
  (hweightSum : ∑ i, weight i = 1) :
-- imply
  (∑ i, weight i * rlc_twoChannelFullIndexed_actualConnectorFibreMass gamma gamma' p q (omega i)) ≤ FK.bcEventMass (rlc_twoChannelFullInnerGraph gamma gamma') (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma') p q (rlc_twoChannelFullInnerExteriorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullIndexed_actualConnectorMixture_le_maxSupported gamma gamma' hp hp1 hq weight hweight hweightSum omega

/--
[rlc_twoChannelFullIndexed_innerEvent_le_merged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullIndexed_innerEvent_le_merged_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {psi : ConfigSpace (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma'))}
  {A : Set (ConfigSpace (Sym2 (RlcTwoChannelFullInnerVertex gamma gamma')))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hwire : rlc_twoChannelFullInnerInducedWiring gamma gamma' psi ≤ rlc_twoChannelFullInnerMergedWiring gamma gamma')
  (hA : IsIncreasing A) :
-- imply
  (∑ rho, (FK.ocd_innerRestrict (rlc_twoChannelFullInnerOuterVertex gamma gamma') ⁻¹' A).indicator (fun _ => (1 : Real)) rho * FK.condBcProb (rlc_twoChannelIndexedOuterGraph gamma gamma') (Lattice.boundaryCliqueGraph (fun _ => False)) p q (FK.ocd_innerEdgeFinset (rlc_twoChannelFullInnerOuterVertex gamma gamma')) psi rho) ≤ FK.bcEventMass (rlc_twoChannelFullInnerGraph gamma gamma') (rlc_twoChannelFullInnerMergedWiring gamma gamma') p q A := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullIndexed_innerEvent_le_merged gamma gamma' hp hp1 hq psi hwire A hA

/--
[rlc_twoChannelFullIndexed_innerEvent_half_q_one_eq_merged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullIndexed_innerEvent_half_q_one_eq_merged_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {psi : ConfigSpace (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma'))}
  {A : Set (ConfigSpace (Sym2 (RlcTwoChannelFullInnerVertex gamma gamma')))} :
-- imply
  (∑ rho, (FK.ocd_innerRestrict (rlc_twoChannelFullInnerOuterVertex gamma gamma') ⁻¹' A).indicator (fun _ => (1 : Real)) rho * FK.condBcProb (rlc_twoChannelIndexedOuterGraph gamma gamma') (Lattice.boundaryCliqueGraph (fun _ => False)) (1 / 2) 1 (FK.ocd_innerEdgeFinset (rlc_twoChannelFullInnerOuterVertex gamma gamma')) psi rho) = FK.bcEventMass (rlc_twoChannelFullInnerGraph gamma gamma') (rlc_twoChannelFullInnerMergedWiring gamma gamma') (1 / 2) 1 A := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullIndexed_innerEvent_half_q_one_eq_merged gamma gamma' psi A

/--
[rlc_twoChannelFullIndexed_fibreMixture_half_q_one_eq_merged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullIndexed_fibreMixture_half_q_one_eq_merged_eq
  {n : Int}
  [Fintype I]
  [DecidableEq I]
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {weight : I → Real}
  {psi : I → ConfigSpace (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma'))}
  {A : Set (ConfigSpace (Sym2 (RlcTwoChannelFullInnerVertex gamma gamma')))}
-- given
  (hweight : ∑ i, weight i = 1) :
-- imply
  (∑ i, weight i * (∑ rho, (FK.ocd_innerRestrict (rlc_twoChannelFullInnerOuterVertex gamma gamma') ⁻¹' A).indicator (fun _ => (1 : Real)) rho * FK.condBcProb (rlc_twoChannelIndexedOuterGraph gamma gamma') (Lattice.boundaryCliqueGraph (fun _ => False)) (1 / 2) 1 (FK.ocd_innerEdgeFinset (rlc_twoChannelFullInnerOuterVertex gamma gamma')) (psi i) rho)) = FK.bcEventMass (rlc_twoChannelFullInnerGraph gamma gamma') (rlc_twoChannelFullInnerMergedWiring gamma gamma') (1 / 2) 1 A := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullIndexed_fibreMixture_half_q_one_eq_merged gamma gamma' weight psi hweight A

/--
[rlc_twoChannelForceTrace_sourceEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelForceTrace_sourceEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {e : RlcTwoChannelFaithfulSourceEdge gamma gamma'} :
-- imply
  rlc_connectorForceTraceConfig gamma gamma' (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) (rlc_twoChannelFaithfulAugmentedEdge e).1 = omega e := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForceTrace_sourceEdge gamma gamma' omega e

/--
[rlc_twoChannelFaithfulDualConfig_open_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFaithfulDualConfig_open_iff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {e : RlcTwoChannelFaithfulSourceEdge gamma gamma'} :
-- imply
  rlc_twoChannelFaithfulDualConfig gamma gamma' omega e = true ↔ (rlc_twoChannelFaithfulAugmentedEdge e).1 ∉ (FK.openSub (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))).edgeSet := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFaithfulDualConfig_open_iff gamma gamma' omega e

/--
[rlc_twoChannelFaithful_indexedOpenGraph_eq_pfdClosedDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFaithful_indexedOpenGraph_eq_pfdClosedDual_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  FK.indexedOpenGraph (rlc_twoChannelFaithfulEnds gamma gamma') (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) = BeffaraDC.pfdClosedDual (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') (FK.openSub (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFaithful_indexedOpenGraph_eq_pfdClosedDual gamma gamma' omega

/--
[rlc_twoChannelFullFaceDual_le_pfdRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullFaceDual_le_pfdRegion_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  openSubgraph 2 (fci_faceDualConfig (rlc_twoChannelFullAmbientConfig gamma gamma' omega)) ≤ whb_faceRegion (jei_pushGraph (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') (FK.openSub (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullFaceDual_le_pfdRegion gamma gamma' omega

/--
[rlc_twoChannelFullFaceDual_eq_pfdRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFullFaceDual_eq_pfdRegion_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  openSubgraph 2 (fci_faceDualConfig (rlc_twoChannelFullAmbientConfig gamma gamma' omega)) = whb_faceRegion (jei_pushGraph (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') (FK.openSub (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullFaceDual_eq_pfdRegion gamma gamma' omega

/--
[rlc_twoChannelFaithful_indexedNumClusters_eq_pfd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFaithful_indexedNumClusters_eq_pfd_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  FK.indexedNumClustersBC (rlc_twoChannelFaithfulEnds gamma gamma') ⊥ (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) = Nat.card (BeffaraDC.pfdClosedDual (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') (FK.openSub (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))).ConnectedComponent := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFaithful_indexedNumClusters_eq_pfd gamma gamma' omega

/--
[rlc_twoChannelFaithful_indexedEdgeProduct_eq_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFaithful_indexedEdgeProduct_eq_source_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p : Real}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  FK.edgeProduct (rlc_connectorTwoChannelGraph gamma gamma') (1 - p) (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) = FK.indexedEdgeProduct p (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFaithful_indexedEdgeProduct_eq_source gamma gamma' p omega

/--
[rlc_twoChannelFaithful_pfdDualEdgeFactor_eq_indexed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFaithful_pfdDualEdgeFactor_eq_indexed_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p : Real}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma' let forced := rlc_connectorForceTraceConfig gamma gamma' (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) BeffaraDC.edgeProductCount p P.G.edgeFinset.card (P.G.edgeFinset.card - (FK.openSub P.G forced).edgeSet.ncard) = (1 - p) ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card * FK.indexedEdgeProduct p (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFaithful_pfdDualEdgeFactor_eq_indexed gamma gamma' p omega

/--
[rlc_twoChannelFaithful_pfdDualWeight_eq_indexed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFaithful_pfdDualWeight_eq_indexed_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  BeffaraDC.pfdDualWeight (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') p q (FK.openSub (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))) = (1 - p) ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card * FK.indexedBcWeight (rlc_twoChannelFaithfulEnds gamma gamma') ⊥ p q (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFaithful_pfdDualWeight_eq_indexed gamma gamma' p q omega

/--
[rlc_twoChannelFaithfulDualEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFaithfulDualEquiv_apply_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  rlc_twoChannelFaithfulDualEquiv gamma gamma' omega = rlc_twoChannelFaithfulDualConfig gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFaithfulDualEquiv_apply gamma gamma' omega

/--
[rlc_twoChannelFaithfulForcedDualEdgeZ_eq_indexed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFaithfulForcedDualEdgeZ_eq_indexed_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real} :
-- imply
  rlc_twoChannelFaithfulForcedDualEdgeZ gamma gamma' p q = (1 - p) ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card * FK.indexedBcZ (rlc_twoChannelFaithfulEnds gamma gamma') ⊥ p q := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFaithfulForcedDualEdgeZ_eq_indexed gamma gamma' p q

/--
[rlc_twoChannelFaithfulForcedDualEdgeProb_eq_indexed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFaithfulForcedDualEdgeProb_eq_indexed_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p : Real}
  {q : Real}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hp1 : p < 1) :
-- imply
  rlc_twoChannelFaithfulForcedDualEdgeProb gamma gamma' p q omega = FK.indexedBcProb (rlc_twoChannelFaithfulEnds gamma gamma') ⊥ p q (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFaithfulForcedDualEdgeProb_eq_indexed gamma gamma' hp1 q omega

/--
[rlc_twoChannelFaithfulForcedDualEdgeEventMass_eq_indexed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFaithfulForcedDualEdgeEventMass_eq_indexed_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p : Real}
  {q : Real}
  {A : Set (ConfigSpace (RlcTwoChannelFaithfulSourceEdge gamma gamma'))}
-- given
  (hp1 : p < 1) :
-- imply
  rlc_twoChannelFaithfulForcedDualEdgeEventMass gamma gamma' p q A = FK.indexedBcEventMass (rlc_twoChannelFaithfulEnds gamma gamma') ⊥ p q A := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFaithfulForcedDualEdgeEventMass_eq_indexed gamma gamma' hp1 q A

/--
[rlc_twoChannelFaithful_pfdDualWeight_edgeConfigCombine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFaithful_pfdDualWeight_edgeConfigCombine_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {outside : RlcTwoChannelOffGraphConfig gamma gamma'} :
-- imply
  BeffaraDC.pfdDualWeight (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') p q (FK.openSub (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' (rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside))) = BeffaraDC.pfdDualWeight (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') p q (FK.openSub (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFaithful_pfdDualWeight_edgeConfigCombine gamma gamma' p q omega outside

/--
[rlc_twoChannelForcedDualZ_eq_offGraph_mul_edgeZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualZ_eq_offGraph_mul_edgeZ_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real} :
-- imply
  rlc_twoChannelForcedDualZ gamma gamma' p q = Fintype.card (RlcTwoChannelOffGraphConfig gamma gamma') * rlc_twoChannelFaithfulForcedDualEdgeZ gamma gamma' p q := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualZ_eq_offGraph_mul_edgeZ gamma gamma' p q

/--
[rlc_twoChannelFaithfulForcedDualEdgeZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFaithfulForcedDualEdgeZ_pos_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < rlc_twoChannelFaithfulForcedDualEdgeZ gamma gamma' p q := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFaithfulForcedDualEdgeZ_pos gamma gamma' hp hp1 hq

/--
[rlc_twoChannelForcedDualProb_extend_mul_offGraph_eq_edgeProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualProb_extend_mul_offGraph_eq_edgeProb_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  Fintype.card (RlcTwoChannelOffGraphConfig gamma gamma') * rlc_twoChannelForcedDualProb gamma gamma' p q (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) = rlc_twoChannelFaithfulForcedDualEdgeProb gamma gamma' p q omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualProb_extend_mul_offGraph_eq_edgeProb gamma gamma' hp hp1 hq omega

/--
[rlc_twoChannelForcedDualEventMass_faithfulPullback_eq_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_faithfulPullback_eq_edge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {A : Set (ConfigSpace (RlcTwoChannelFaithfulSourceEdge gamma gamma'))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' p q (rlc_twoChannelFaithfulFullPullbackEvent gamma gamma' A) = rlc_twoChannelFaithfulForcedDualEdgeEventMass gamma gamma' p q A := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_faithfulPullback_eq_edge gamma gamma' hp hp1 hq A

/--
[rlc_twoChannelFaithfulFaceSeparateWiring_le_merged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFaithfulFaceSeparateWiring_le_merged_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  rlc_twoChannelFaithfulFaceSeparateWiring gamma gamma' ≤ rlc_twoChannelFaithfulFaceMergedWiring gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFaithfulFaceSeparateWiring_le_merged gamma gamma'

/--
[rlc_twoChannelFaithfulFaceConnectorEvent_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFaithfulFaceConnectorEvent_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
-- imply
  rlc_twoChannelFaithfulDualConfig gamma gamma' omega ∈ rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFaithfulFaceConnectorEvent_of_failure gamma gamma' hfaith omega hno

/--
[rlc_twoChannelFaithfulFaceConnectorEvent_to_ambientReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFaithfulFaceConnectorEvent_to_ambientReachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hconn : rlc_twoChannelFaithfulDualConfig gamma gamma' omega ∈ rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') :
-- imply
  ∃ x y : RlcConnectorVertex n, rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧ (openSubgraph 2 (rlc_dualReflectConfig (rlc_twoChannelFullAmbientConfig gamma gamma' omega))).Reachable x.1 y.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFaithfulFaceConnectorEvent_to_ambientReachable gamma gamma' omega hconn

/--
[rlc_twoChannelFaithfulFaceConnectorEvent_to_indexedOuterReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFaithfulFaceConnectorEvent_to_indexedOuterReachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hconn : rlc_twoChannelFaithfulDualConfig gamma gamma' omega ∈ rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') :
-- imply
  ∃ x y : RlcConnectorVertex n, rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧ (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Reachable (rlc_twoChannelIndexedOuterTarget gamma gamma' x) (rlc_twoChannelIndexedOuterTarget gamma gamma' y) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFaithfulFaceConnectorEvent_to_indexedOuterReachable gamma gamma' omega hconn

/--
[rlc_twoChannelFaithfulFaceConnectorEvent_iff_indexedOuterReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFaithfulFaceConnectorEvent_iff_indexedOuterReachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  rlc_twoChannelFaithfulDualConfig gamma gamma' omega ∈ rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma' ↔ ∃ x y : RlcConnectorVertex n, rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧ (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Reachable (rlc_twoChannelIndexedOuterTarget gamma gamma' x) (rlc_twoChannelIndexedOuterTarget gamma gamma' y) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFaithfulFaceConnectorEvent_iff_indexedOuterReachable gamma gamma' omega

/--
[rlc_twoChannelFailure_to_indexedOuterReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFailure_to_indexedOuterReachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
-- imply
  ∃ x y : RlcConnectorVertex n, rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧ (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Reachable (rlc_twoChannelIndexedOuterTarget gamma gamma' x) (rlc_twoChannelIndexedOuterTarget gamma gamma' y) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFailure_to_indexedOuterReachable gamma gamma' hfaith omega hno

/--
[rlc_twoChannelFaithfulFaceConnectorEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFaithfulFaceConnectorEvent_isIncreasing_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  IsIncreasing (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFaithfulFaceConnectorEvent_isIncreasing gamma gamma'

/--
[rlc_twoChannelFaithfulFaceFree_le_merged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFaithfulFaceFree_le_merged_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  (⊥ : SimpleGraph (RlcTwoChannelFaithfulFace gamma gamma')) ≤ rlc_twoChannelFaithfulFaceMergedWiring gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFaithfulFaceFree_le_merged gamma gamma'

/--
[rlc_twoChannelFaithfulFaceIndexedMass_free_le_merged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFaithfulFaceIndexedMass_free_le_merged_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  FK.indexedBcEventMass (rlc_twoChannelFaithfulEnds gamma gamma') ⊥ p q (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') ≤ FK.indexedBcEventMass (rlc_twoChannelFaithfulEnds gamma gamma') (rlc_twoChannelFaithfulFaceMergedWiring gamma gamma') p q (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFaithfulFaceIndexedMass_free_le_merged gamma gamma' hp hp1 hq

/--
[rlc_twoChannelFaithfulForcedDualEdgeConnectorMass_le_merged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFaithfulForcedDualEdgeConnectorMass_le_merged_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  rlc_twoChannelFaithfulForcedDualEdgeEventMass gamma gamma' p q (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') ≤ FK.indexedBcEventMass (rlc_twoChannelFaithfulEnds gamma gamma') (rlc_twoChannelFaithfulFaceMergedWiring gamma gamma') p q (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFaithfulForcedDualEdgeConnectorMass_le_merged gamma gamma' hp hp1 hq

/--
[rlc_twoChannelFailure_subset_faithfulFacePullback](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFailure_subset_faithfulFacePullback_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ ⊆ rlc_twoChannelFaithfulFullPullbackEvent gamma gamma' (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFailure_subset_faithfulFacePullback gamma gamma' hfaith

/--
[rlc_twoChannelForcedDualFailureMass_le_faithfulMerged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualFailureMass_le_faithfulMerged_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' p q (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ ≤ FK.indexedBcEventMass (rlc_twoChannelFaithfulEnds gamma gamma') (rlc_twoChannelFaithfulFaceMergedWiring gamma gamma') p q (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualFailureMass_le_faithfulMerged gamma gamma' hfaith hp hp1 hq

/--
[rlc_twoChannelFaithfulFaceIndexedMass_mono_merged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean)
-/
@[path]
private lemma rlc_twoChannelFaithfulFaceIndexedMass_mono_merged_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  FK.indexedBcEventMass (rlc_twoChannelFaithfulEnds gamma gamma') (rlc_twoChannelFaithfulFaceSeparateWiring gamma gamma') p q (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') ≤ FK.indexedBcEventMass (rlc_twoChannelFaithfulEnds gamma gamma') (rlc_twoChannelFaithfulFaceMergedWiring gamma gamma') p q (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFaithfulFaceIndexedMass_mono_merged gamma gamma' hp hp1 hq


-- created on 2026-10-23
