import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part12
open Finset SimpleGraph StatMech.Lattice StatMech StatMech.BeffaraDC StatMech.BeffaraDC.SymmetricDomain


/--
[onGammaOne_gammaOneStart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma onGammaOne_gammaOneStart_eq
  {D : SymmetricDomain} :
-- imply
  D.OnGammaOne D.gammaOneStart := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.onGammaOne_gammaOneStart D

/--
[onGammaTwo_gammaTwoStart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma onGammaTwo_gammaTwoStart_eq
  {D : SymmetricDomain} :
-- imply
  D.OnGammaTwo D.gammaTwoStart := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.onGammaTwo_gammaTwoStart D

/--
[mixedConnected_iff_openConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma mixedConnected_iff_openConnected_eq
  {D : SymmetricDomain}
  {omega : ConfigSpace (Sym2 D.Vertex)} :
-- imply
  D.MixedConnected omega ↔ D.OpenConnected omega := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.mixedConnected_iff_openConnected D omega

/--
[mixedConnectionProbability_eq_openConnectionProbability](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma mixedConnectionProbability_eq_openConnectionProbability_eq
  {D : SymmetricDomain}
  {q : Real} :
-- imply
  D.mixedConnectionProbability q = D.openConnectionProbability q := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.mixedConnectionProbability_eq_openConnectionProbability D q

/--
[mixedConnection_add_disconnection_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma mixedConnection_add_disconnection_eq_one_eq
  {D : SymmetricDomain}
  {q : Real}
-- given
  (hq : 1 ≤ q) :
-- imply
  D.mixedConnectionProbability q + D.mixedDisconnectionProbability q = 1 := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.mixedConnection_add_disconnection_eq_one D hq

/--
[MixedDualComplementRN.card_disconnected_eq_card_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma card_disconnected_eq_card_connected_eq
  {D : SymmetricDomain}
  {q : Real}
  {R : MixedDualComplementRN D q} :
-- imply
  Fintype.card {omega : ConfigSpace (Sym2 D.Vertex) // ¬D.MixedConnected omega} = Fintype.card {eta : ConfigSpace (Sym2 D.Vertex) // D.MixedConnected eta} := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.MixedDualComplementRN.card_disconnected_eq_card_connected R

/--
[MixedDualComplementRN.exists_connected_and_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma exists_connected_and_disconnected_eq
  {D : SymmetricDomain}
  {q : Real}
  {R : MixedDualComplementRN D q} :
-- imply
  (∃ omega, D.MixedConnected omega) ∧ ∃ eta, ¬D.MixedConnected eta := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.MixedDualComplementRN.exists_connected_and_disconnected R

/--
[mixedConnected_all_of_boundaryBlocksOverlap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma mixedConnected_all_of_boundaryBlocksOverlap_eq
  {D : SymmetricDomain}
  {omega : ConfigSpace (Sym2 D.Vertex)}
-- given
  (h : D.BoundaryBlocksOverlap) :
-- imply
  D.MixedConnected omega := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.mixedConnected_all_of_boundaryBlocksOverlap D h omega

/--
[no_mixedDualComplementRN_of_boundaryBlocksOverlap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma no_mixedDualComplementRN_of_boundaryBlocksOverlap_eq
  {D : SymmetricDomain}
  {q : Real}
-- given
  (h : D.BoundaryBlocksOverlap) :
-- imply
  MixedDualComplementRN D q → False := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.no_mixedDualComplementRN_of_boundaryBlocksOverlap D q h

/--
[overlappingSingletonDomain_boundaryBlocksOverlap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma overlappingSingletonDomain_boundaryBlocksOverlap_eq :
-- imply
  overlappingSingletonDomain.BoundaryBlocksOverlap := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.overlappingSingletonDomain_boundaryBlocksOverlap

/--
[overlappingSingletonDomain_no_mixedDualComplementRN](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma overlappingSingletonDomain_no_mixedDualComplementRN_eq
  {q : Real} :
-- imply
  MixedDualComplementRN overlappingSingletonDomain q → False := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.overlappingSingletonDomain_no_mixedDualComplementRN q

/--
[disjointDisconnectedDomain_boundaryBlocksDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma disjointDisconnectedDomain_boundaryBlocksDisjoint_eq :
-- imply
  ¬disjointDisconnectedDomain.BoundaryBlocksOverlap := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.disjointDisconnectedDomain_boundaryBlocksDisjoint

/--
[disjointDisconnectedDomain_finiteGraph_no_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma disjointDisconnectedDomain_finiteGraph_no_adj_eq
  {x y : disjointDisconnectedDomain.Vertex} :
-- imply
  ¬disjointDisconnectedDomain.finiteGraph.Adj x y := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.disjointDisconnectedDomain_finiteGraph_no_adj x y

/--
[disjointDisconnectedDomain_mixedWiring_no_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma disjointDisconnectedDomain_mixedWiring_no_adj_eq
  {x y : disjointDisconnectedDomain.Vertex} :
-- imply
  ¬disjointDisconnectedDomain.mixedWiring.Adj x y := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.disjointDisconnectedDomain_mixedWiring_no_adj x y

/--
[disjointDisconnectedDomain_not_mixedConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma disjointDisconnectedDomain_not_mixedConnected_eq
  {omega : ConfigSpace (Sym2 disjointDisconnectedDomain.Vertex)} :
-- imply
  ¬disjointDisconnectedDomain.MixedConnected omega := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.disjointDisconnectedDomain_not_mixedConnected omega

/--
[disjointDisconnectedDomain_no_mixedDualComplementRN](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma disjointDisconnectedDomain_no_mixedDualComplementRN_eq
  {q : Real} :
-- imply
  MixedDualComplementRN disjointDisconnectedDomain q → False := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.disjointDisconnectedDomain_no_mixedDualComplementRN q

/--
[connectedVDomain_vertex_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma connectedVDomain_vertex_cases_eq
  {x : connectedVDomain.Vertex} :
-- imply
  x = connectedVAxis ∨ x = connectedVLeft ∨ x = connectedVRight := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.connectedVDomain_vertex_cases x

/--
[connectedVDomain_left_axis_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma connectedVDomain_left_axis_adj_eq :
-- imply
  connectedVDomain.finiteGraph.Adj connectedVLeft connectedVAxis := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.connectedVDomain_left_axis_adj

/--
[connectedVDomain_axis_right_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma connectedVDomain_axis_right_adj_eq :
-- imply
  connectedVDomain.finiteGraph.Adj connectedVAxis connectedVRight := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.connectedVDomain_axis_right_adj

/--
[connectedVDomain_finiteGraph_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma connectedVDomain_finiteGraph_connected_eq :
-- imply
  connectedVDomain.finiteGraph.Connected := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.connectedVDomain_finiteGraph_connected

/--
[connectedVDomain_boundaryBlocksDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma connectedVDomain_boundaryBlocksDisjoint_eq :
-- imply
  ¬connectedVDomain.BoundaryBlocksOverlap := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.connectedVDomain_boundaryBlocksDisjoint

/--
[connectedV_edges_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma connectedV_edges_ne_eq :
-- imply
  connectedVLeftEdge ≠ connectedVRightEdge := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.connectedV_edges_ne

/--
[connectedVDomain_mixedConnected_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma connectedVDomain_mixedConnected_iff_eq
  {omega : ConfigSpace (Sym2 connectedVDomain.Vertex)} :
-- imply
  connectedVDomain.MixedConnected omega ↔ omega connectedVLeftEdge = true ∧ omega connectedVRightEdge = true := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.connectedVDomain_mixedConnected_iff omega

/--
[card_config_eq_four_mul_twoCoordinateRemainder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma card_config_eq_four_mul_twoCoordinateRemainder_eq
  [Fintype E]
  [DecidableEq E]
  {a b : E}
-- given
  (hab : a ≠ b) :
-- imply
  Fintype.card (E → Bool) = 4 * Fintype.card (TwoCoordinateRemainder a b hab → Bool) := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.card_config_eq_four_mul_twoCoordinateRemainder a b hab

/--
[card_not_twoCoordinateTrue_eq_three_mul_card_twoCoordinateTrue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma card_not_twoCoordinateTrue_eq_three_mul_card_twoCoordinateTrue_eq
  [Fintype E]
  [DecidableEq E]
  {a b : E}
-- given
  (hab : a ≠ b) :
-- imply
  Fintype.card {omega : E → Bool // ¬(omega a = true ∧ omega b = true)} = 3 * Fintype.card {omega : E → Bool // omega a = true ∧ omega b = true} := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.card_not_twoCoordinateTrue_eq_three_mul_card_twoCoordinateTrue a b hab

/--
[card_not_twoCoordinateTrue_ne_card_twoCoordinateTrue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma card_not_twoCoordinateTrue_ne_card_twoCoordinateTrue_eq
  [Fintype E]
  [DecidableEq E]
  {a b : E}
-- given
  (hab : a ≠ b) :
-- imply
  Fintype.card {omega : E → Bool // ¬(omega a = true ∧ omega b = true)} ≠ Fintype.card {omega : E → Bool // omega a = true ∧ omega b = true} := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.card_not_twoCoordinateTrue_ne_card_twoCoordinateTrue a b hab

/--
[connectedVDomain_card_disconnected_eq_three_mul_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma connectedVDomain_card_disconnected_eq_three_mul_connected_eq :
-- imply
  Fintype.card {omega : ConfigSpace (Sym2 connectedVDomain.Vertex) // ¬connectedVDomain.MixedConnected omega} = 3 * Fintype.card {omega : ConfigSpace (Sym2 connectedVDomain.Vertex) // connectedVDomain.MixedConnected omega} := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.connectedVDomain_card_disconnected_eq_three_mul_connected

/--
[connectedVDomain_no_mixedDualComplementRN](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma connectedVDomain_no_mixedDualComplementRN_eq
  {q : Real} :
-- imply
  MixedDualComplementRN connectedVDomain q → False := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.connectedVDomain_no_mixedDualComplementRN q

/--
[mixedDisconnectionProbability_eq_dualPull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma mixedDisconnectionProbability_eq_dualPull_eq
  {D : SymmetricDomain}
  {q : Real}
  {R : MixedDualComplementRN D q} :
-- imply
  D.mixedDisconnectionProbability q = ∑ eta : ConfigSpace (Sym2 D.Vertex), if D.MixedConnected eta then D.mixedMass q (R.dual.symm eta) else 0 := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.mixedDisconnectionProbability_eq_dualPull D q R

/--
[mixedDisconnectionProbability_le_q_sq_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma mixedDisconnectionProbability_le_q_sq_mul_eq
  {D : SymmetricDomain}
  {q : Real}
  {R : MixedDualComplementRN D q} :
-- imply
  D.mixedDisconnectionProbability q ≤ q ^ 2 * D.mixedConnectionProbability q := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.mixedDisconnectionProbability_le_q_sq_mul D q R

/--
[mixedConnectionProbability_ge_one_div_one_add_q_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma mixedConnectionProbability_ge_one_div_one_add_q_sq_eq
  {D : SymmetricDomain}
  {q : Real}
  {R : MixedDualComplementRN D q}
-- given
  (hq : 1 ≤ q) :
-- imply
  1 / (1 + q ^ 2) ≤ D.mixedConnectionProbability q := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.mixedConnectionProbability_ge_one_div_one_add_q_sq D hq R

/--
[openConnectionProbability_ge_one_div_one_add_q_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma openConnectionProbability_ge_one_div_one_add_q_sq_eq
  {D : SymmetricDomain}
  {q : Real}
  {R : MixedDualComplementRN D q}
-- given
  (hq : 1 ≤ q) :
-- imply
  1 / (1 + q ^ 2) ≤ D.openConnectionProbability q := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.openConnectionProbability_ge_one_div_one_add_q_sq D hq R

/--
[unionConnected_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma unionConnected_all_eq
  {D : SymmetricDomain}
  {omega : ConfigSpace (Sym2 D.Vertex)} :
-- imply
  D.UnionConnected omega := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.unionConnected_all D omega

/--
[no_unionWiring_dual_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean)
-/
@[path]
private lemma no_unionWiring_dual_complement_eq
  {D : SymmetricDomain} :
-- imply
  ¬∃ dual : ConfigSpace (Sym2 D.Vertex) ≃ ConfigSpace (Sym2 D.Vertex), ∀ omega, D.UnionConnected (dual omega) ↔ ¬D.UnionConnected omega := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.no_unionWiring_dual_complement D


-- created on 2026-10-23
