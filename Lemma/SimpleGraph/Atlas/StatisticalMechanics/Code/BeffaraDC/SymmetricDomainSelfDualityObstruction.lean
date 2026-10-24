import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDualityObstruction
open Set SimpleGraph StatMech.Lattice StatMech StatMech.BeffaraDC StatMech.BeffaraDC.SymmetricDomain


/--
[mixedDualComplementRN_isEmpty_of_all_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma mixedDualComplementRN_isEmpty_of_all_connected_eq
  {D : SymmetricDomain}
  {q : Real}
-- given
  (hall : ∀ omega, D.MixedConnected omega) :
-- imply
  IsEmpty (MixedDualComplementRN D q) := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.mixedDualComplementRN_isEmpty_of_all_connected D q hall

/--
[mixedDualComplementRN_isEmpty_of_all_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma mixedDualComplementRN_isEmpty_of_all_disconnected_eq
  {D : SymmetricDomain}
  {q : Real}
-- given
  (hall : ∀ omega, ¬D.MixedConnected omega) :
-- imply
  IsEmpty (MixedDualComplementRN D q) := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.mixedDualComplementRN_isEmpty_of_all_disconnected D q hall

/--
[degenerate_openConnected_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma degenerate_openConnected_all_eq
  {omega : ConfigSpace (Sym2 degenerateSymmetricDomain.Vertex)} :
-- imply
  degenerateSymmetricDomain.OpenConnected omega := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.degenerate_openConnected_all omega

/--
[degenerate_mixedConnected_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma degenerate_mixedConnected_all_eq
  {omega : ConfigSpace (Sym2 degenerateSymmetricDomain.Vertex)} :
-- imply
  degenerateSymmetricDomain.MixedConnected omega := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.degenerate_mixedConnected_all omega

/--
[degenerate_mixedDualComplementRN_isEmpty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma degenerate_mixedDualComplementRN_isEmpty_eq
  {q : Real} :
-- imply
  IsEmpty (MixedDualComplementRN degenerateSymmetricDomain q) := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.degenerate_mixedDualComplementRN_isEmpty q

/--
[diagReflFun_separatedSiteOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma diagReflFun_separatedSiteOne_eq :
-- imply
  diagReflFun separatedSiteOne = separatedSiteTwo := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.diagReflFun_separatedSiteOne

/--
[diagReflFun_separatedSiteTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma diagReflFun_separatedSiteTwo_eq :
-- imply
  diagReflFun separatedSiteTwo = separatedSiteOne := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.diagReflFun_separatedSiteTwo

/--
[separated_finiteGraph_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma separated_finiteGraph_eq_bot_eq :
-- imply
  separatedSymmetricDomain.finiteGraph = ⊥ := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.separated_finiteGraph_eq_bot

/--
[separated_not_openConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma separated_not_openConnected_eq
  {omega : ConfigSpace (Sym2 separatedSymmetricDomain.Vertex)} :
-- imply
  ¬separatedSymmetricDomain.OpenConnected omega := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.separated_not_openConnected omega

/--
[separated_not_mixedConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma separated_not_mixedConnected_eq
  {omega : ConfigSpace (Sym2 separatedSymmetricDomain.Vertex)} :
-- imply
  ¬separatedSymmetricDomain.MixedConnected omega := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.separated_not_mixedConnected omega

/--
[separated_openConnectionProbability_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma separated_openConnectionProbability_eq_zero_eq
  {q : Real} :
-- imply
  separatedSymmetricDomain.openConnectionProbability q = 0 := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.separated_openConnectionProbability_eq_zero q

/--
[separated_selfDuality_lower_bound_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma separated_selfDuality_lower_bound_false_eq :
-- imply
  ¬(1 / (1 + (1 : Real) ^ 2) ≤ separatedSymmetricDomain.openConnectionProbability 1) := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.separated_selfDuality_lower_bound_false

/--
[separated_mixedDualComplementRN_isEmpty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma separated_mixedDualComplementRN_isEmpty_eq
  {q : Real} :
-- imply
  IsEmpty (MixedDualComplementRN separatedSymmetricDomain q) := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.separated_mixedDualComplementRN_isEmpty q

/--
[diagReflFun_connectedBridgeSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma diagReflFun_connectedBridgeSite_eq :
-- imply
  diagReflFun connectedBridgeSite = connectedBridgeSite := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.diagReflFun_connectedBridgeSite

/--
[connected_adj_one_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma connected_adj_one_bridge_eq :
-- imply
  connectedSymmetricDomain.finiteGraph.Adj connectedVertexOne connectedVertexBridge := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.connected_adj_one_bridge

/--
[connected_adj_two_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma connected_adj_two_bridge_eq :
-- imply
  connectedSymmetricDomain.finiteGraph.Adj connectedVertexTwo connectedVertexBridge := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.connected_adj_two_bridge

/--
[bcProb_one_eq_fkProb_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma bcProb_one_eq_fkProb_one_eq
  [Fintype V]
  [DecidableEq V]
  {G C : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel C.Adj]
  {p : Real}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  FK.bcProb G C p 1 omega = FK.fkProb G p 1 omega := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.bcProb_one_eq_fkProb_one G C p omega

/--
[connected_vertex_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma connected_vertex_cases_eq
  {z : connectedSymmetricDomain.Vertex} :
-- imply
  z = connectedVertexOne ∨ z = connectedVertexTwo ∨ z = connectedVertexBridge := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.connected_vertex_cases z

/--
[connected_vertex_one_ne_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma connected_vertex_one_ne_two_eq :
-- imply
  connectedVertexOne ≠ connectedVertexTwo := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.connected_vertex_one_ne_two

/--
[connected_finiteGraph_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma connected_finiteGraph_connected_eq :
-- imply
  connectedSymmetricDomain.finiteGraph.Connected := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.connected_finiteGraph_connected

/--
[connected_boundary_paths_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma connected_boundary_paths_disjoint_eq :
-- imply
  connectedSymmetricDomain.γ₁.support ∩ connectedSymmetricDomain.γ₂.support = ∅ := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.connected_boundary_paths_disjoint

/--
[connected_openConnected_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma connected_openConnected_iff_eq
  {omega : ConfigSpace (Sym2 connectedSymmetricDomain.Vertex)} :
-- imply
  connectedSymmetricDomain.OpenConnected omega ↔ omega s(connectedVertexOne, connectedVertexBridge) = true ∧ omega s(connectedVertexTwo, connectedVertexBridge) = true := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.connected_openConnected_iff omega

/--
[connectedRequiredEdges_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma connectedRequiredEdges_subset_eq :
-- imply
  connectedRequiredEdges ⊆ connectedSymmetricDomain.finiteGraph.edgeFinset := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.connectedRequiredEdges_subset

/--
[connectedRequiredEdges_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma connectedRequiredEdges_card_eq :
-- imply
  connectedRequiredEdges.card = 2 := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.connectedRequiredEdges_card

/--
[connected_openConnectionProbability_eq_quarter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma connected_openConnectionProbability_eq_quarter_eq :
-- imply
  connectedSymmetricDomain.openConnectionProbability 1 = 1 / 4 := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.connected_openConnectionProbability_eq_quarter

/--
[connected_selfDuality_lower_bound_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma connected_selfDuality_lower_bound_false_eq :
-- imply
  ¬(1 / (1 + (1 : Real) ^ 2) ≤ connectedSymmetricDomain.openConnectionProbability 1) := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.connected_selfDuality_lower_bound_false

/--
[connected_mixedDualComplementRN_isEmpty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma connected_mixedDualComplementRN_isEmpty_eq :
-- imply
  IsEmpty (MixedDualComplementRN connectedSymmetricDomain 1) := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.connected_mixedDualComplementRN_isEmpty

/--
[not_all_symmetricDomain_selfDuality_lower_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma not_all_symmetricDomain_selfDuality_lower_bounds_eq :
-- imply
  ¬∀ D : SymmetricDomain, 1 / (1 + (1 : Real) ^ 2) ≤ D.openConnectionProbability 1 := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.not_all_symmetricDomain_selfDuality_lower_bounds

/--
[no_universal_mixedDualComplementRN](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean)
-/
@[path]
private lemma no_universal_mixedDualComplementRN_eq
  {q : Real} :
-- imply
  ¬∀ D : SymmetricDomain, Nonempty (MixedDualComplementRN D q) := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.no_universal_mixedDualComplementRN q


-- created on 2026-10-23
