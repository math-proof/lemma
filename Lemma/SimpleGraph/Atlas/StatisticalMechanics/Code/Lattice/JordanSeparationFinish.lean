import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFinish.Part2
open SimpleGraph Set StatMech StatMech.Lattice


/--
[jsf_deleteEdges_sup_edge_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFinish.lean)
-/
@[path]
private lemma jsf_deleteEdges_sup_edge_eq_eq
  {G : SimpleGraph V}
  {a b : V}
-- given
  (he : s(a, b) ∈ G.edgeSet) :
-- imply
  G = (G.deleteEdges {s(a, b)}) ⊔ edge a b := by
-- proof
  apply StatMech.Lattice.jsf_deleteEdges_sup_edge_eq G a b he

/--
[jsf_card_components_sup_edge_keep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFinish.lean)
-/
@[path]
private lemma jsf_card_components_sup_edge_keep_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b : V}
-- given
  (hab : G.Reachable a b) :
-- imply
  Nat.card (G ⊔ edge a b).ConnectedComponent = Nat.card G.ConnectedComponent := by
-- proof
  apply StatMech.Lattice.jsf_card_components_sup_edge_keep G hab

/--
[jsf_card_components_sup_edge_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFinish.lean)
-/
@[path]
private lemma jsf_card_components_sup_edge_merge_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  [Empty.Finite G.ConnectedComponent]
  {a b : V}
-- given
  (hab : ¬ G.Reachable a b) :
-- imply
  Nat.card (G ⊔ edge a b).ConnectedComponent + 1 = Nat.card G.ConnectedComponent := by
-- proof
  apply StatMech.Lattice.jsf_card_components_sup_edge_merge G hab

/--
[jsf_mem_edgeSet_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFinish.lean)
-/
@[path]
private lemma jsf_mem_edgeSet_edge_eq
  {p q : Site 2}
  {e : Sym2 (Site 2)}
-- given
  (hpq : p ≠ q) :
-- imply
  e ∈ (edge p q).edgeSet ↔ e = s(p, q) := by
-- proof
  apply StatMech.Lattice.jsf_mem_edgeSet_edge hpq e

/--
[jsf_regionGraph_sup_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFinish.lean)
-/
@[path]
private lemma jsf_regionGraph_sup_edge_eq
  {G : SimpleGraph (Site 2)}
  {p q : Site 2}
-- given
  (hpq : p ≠ q) :
-- imply
  regionGraph (G ⊔ edge p q) = (regionGraph G).deleteEdges {crossEdge s(p, q)} := by
-- proof
  apply StatMech.Lattice.jsf_regionGraph_sup_edge G hpq

/--
[jsf_regionGraph_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFinish.lean)
-/
@[path]
private lemma jsf_regionGraph_bot_eq :
-- imply
  regionGraph (⊥ : SimpleGraph (Site 2)) = hypercubicLattice 2 := by
-- proof
  apply StatMech.Lattice.jsf_regionGraph_bot

/--
[jsf_dual_delete_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFinish.lean)
-/
@[path]
private lemma jsf_dual_delete_dichotomy_eq
  {G : SimpleGraph (Site 2)}
  {p q f g : Site 2}
  [Empty.Finite (regionGraph G).ConnectedComponent]
  [Empty.Finite (regionGraph (G ⊔ edge p q)).ConnectedComponent]
-- given
  (hpq : p ≠ q)
  (hfg : crossEdge s(p, q) = s(f, g))
  (hpres : crossEdge s(p, q) ∈ (regionGraph G).edgeSet) :
-- imply
  (((regionGraph G).deleteEdges {crossEdge s(p, q)}).Reachable f g → Nat.card (regionGraph (G ⊔ edge p q)).ConnectedComponent = Nat.card (regionGraph G).ConnectedComponent) ∧ (¬ ((regionGraph G).deleteEdges {crossEdge s(p, q)}).Reachable f g → Nat.card (regionGraph (G ⊔ edge p q)).ConnectedComponent = Nat.card (regionGraph G).ConnectedComponent + 1) := by
-- proof
  apply StatMech.Lattice.jsf_dual_delete_dichotomy G hpq hfg hpres

/--
[jsf_dualEulerCount_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFinish.lean)
-/
@[path]
private lemma jsf_dualEulerCount_iff_eq
  {P : PlanarZ2Subgraph} :
-- imply
  jsf_PlanarCutCycleDuality P ↔ jcr_DualEulerCount P := by
-- proof
  apply StatMech.Lattice.jsf_dualEulerCount_iff P

/--
[jsf_discreteJordan_of_cutCycleDuality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFinish.lean)
-/
@[path]
private lemma jsf_discreteJordan_of_cutCycleDuality_eq
  {P : PlanarZ2Subgraph}
-- given
  (h : jsf_PlanarCutCycleDuality P) :
-- imply
  DiscreteJordanSeparation P := by
-- proof
  apply StatMech.Lattice.jsf_discreteJordan_of_cutCycleDuality P h

/--
[jsf_discreteJordan_iff_cutCycleDuality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFinish.lean)
-/
@[path]
private lemma jsf_discreteJordan_iff_cutCycleDuality_eq
  {P : PlanarZ2Subgraph} :
-- imply
  DiscreteJordanSeparation P ↔ jsf_PlanarCutCycleDuality P := by
-- proof
  apply StatMech.Lattice.jsf_discreteJordan_iff_cutCycleDuality P

/--
[jsf_geometricRegionCount_eq_nullity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFinish.lean)
-/
@[path]
private lemma jsf_geometricRegionCount_eq_nullity_eq
  {P : PlanarZ2Subgraph}
-- given
  (h : jsf_PlanarCutCycleDuality P) :
-- imply
  geometricRegionCount P = nullity P.G := by
-- proof
  apply StatMech.Lattice.jsf_geometricRegionCount_eq_nullity P h

/--
[jsf_cutCycleDuality_of_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFinish.lean)
-/
@[path]
private lemma jsf_cutCycleDuality_of_bot_eq
  {P : PlanarZ2Subgraph}
-- given
  (hG : P.G = ⊥) :
-- imply
  jsf_PlanarCutCycleDuality P := by
-- proof
  apply StatMech.Lattice.jsf_cutCycleDuality_of_bot hG

/--
[jsf_discreteJordan_of_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFinish.lean)
-/
@[path]
private lemma jsf_discreteJordan_of_bot_eq
  {P : PlanarZ2Subgraph}
-- given
  (hG : P.G = ⊥) :
-- imply
  DiscreteJordanSeparation P := by
-- proof
  apply StatMech.Lattice.jsf_discreteJordan_of_bot hG


-- created on 2026-10-23
