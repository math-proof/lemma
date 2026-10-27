import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
open SimpleGraph Set StatMech StatMech.Lattice


/--
[jei_sym2_mem_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerInduction.lean)
-/
@[path]
private lemma jei_sym2_mem_finite_eq
  {e : Sym2 (Site 2)} :
-- imply
  {x : Site 2 | x ∈ e}.Finite := by
-- proof
  apply StatMech.Lattice.jei_sym2_mem_finite e

/--
[jei_support_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerInduction.lean)
-/
@[path]
private lemma jei_support_finite_eq
  {H : SimpleGraph (Site 2)}
-- given
  (hfin : H.edgeSet.Finite) :
-- imply
  H.support.Finite := by
-- proof
  apply StatMech.Lattice.jei_support_finite H hfin

/--
[jei_exterior_dual_edge_not_deleted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerInduction.lean)
-/
@[path]
private lemma jei_exterior_dual_edge_not_deleted_eq
  {H : SimpleGraph (Site 2)}
  {R : ℕ}
  {f g : Site 2}
-- given
  (hR : ∀ v ∈ H.support, v ∈ box 2 R)
  (hf : f ∉ box 2 R) :
-- imply
  crossEdge.symm s(f, g) ∉ H.edgeSet := by
-- proof
  apply StatMech.Lattice.jei_exterior_dual_edge_not_deleted H R hR hf

/--
[jei_regionGraph_adj_of_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerInduction.lean)
-/
@[path]
private lemma jei_regionGraph_adj_of_exterior_eq
  {H : SimpleGraph (Site 2)}
  {R : ℕ}
  {f g : Site 2}
-- given
  (hR : ∀ v ∈ H.support, v ∈ box 2 R)
  (hf : f ∉ box 2 R)
  (hadj : (hypercubicLattice 2).Adj f g) :
-- imply
  (regionGraph H).Adj f g := by
-- proof
  apply StatMech.Lattice.jei_regionGraph_adj_of_exterior H R hR hf hadj

/--
[jei_regionComponents_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerInduction.lean)
-/
@[path]
private lemma jei_regionComponents_finite_eq
  {H : SimpleGraph (Site 2)}
-- given
  (hfin : H.edgeSet.Finite) :
-- imply
  Empty.Finite (regionGraph H).ConnectedComponent := by
-- proof
  apply StatMech.Lattice.jei_regionComponents_finite H hfin

/--
[jei_pushGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerInduction.lean)
-/
@[path]
private lemma jei_pushGraph_adj_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {a b : Site 2} :
-- imply
  (jei_pushGraph P K).Adj a b ↔ ∃ x y : P.V, K.Adj x y ∧ P.emb x = a ∧ P.emb y = b := by
-- proof
  apply StatMech.Lattice.jei_pushGraph_adj P K a b

/--
[jei_pushGraph_G](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerInduction.lean)
-/
@[path]
private lemma jei_pushGraph_G_eq
  {P : PlanarZ2Subgraph} :
-- imply
  jei_pushGraph P P.G = imageGraph P := by
-- proof
  apply StatMech.Lattice.jei_pushGraph_G P

/--
[jei_pushGraph_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerInduction.lean)
-/
@[path]
private lemma jei_pushGraph_bot_eq
  {P : PlanarZ2Subgraph} :
-- imply
  jei_pushGraph P ⊥ = ⊥ := by
-- proof
  apply StatMech.Lattice.jei_pushGraph_bot P

/--
[jei_pushGraph_edgeSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerInduction.lean)
-/
@[path]
private lemma jei_pushGraph_edgeSet_finite_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V} :
-- imply
  (jei_pushGraph P K).edgeSet.Finite := by
-- proof
  apply StatMech.Lattice.jei_pushGraph_edgeSet_finite P K

/--
[jei_pushGraph_regionComponents_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerInduction.lean)
-/
@[path]
private lemma jei_pushGraph_regionComponents_finite_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V} :
-- imply
  Empty.Finite (regionGraph (jei_pushGraph P K)).ConnectedComponent := by
-- proof
  apply StatMech.Lattice.jei_pushGraph_regionComponents_finite P K

/--
[jei_pushGraph_sup_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerInduction.lean)
-/
@[path]
private lemma jei_pushGraph_sup_edge_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {x y : P.V}
-- given
  (hne : x ≠ y) :
-- imply
  jei_pushGraph P (K ⊔ edge x y) = jei_pushGraph P K ⊔ edge (P.emb x) (P.emb y) := by
-- proof
  apply StatMech.Lattice.jei_pushGraph_sup_edge P K x y hne

/--
[jei_push_reachable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerInduction.lean)
-/
@[path]
private lemma jei_push_reachable_iff_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {x y : P.V} :
-- imply
  (jei_pushGraph P K).Reachable (P.emb x) (P.emb y) ↔ K.Reachable x y := by
-- proof
  apply StatMech.Lattice.jei_push_reachable_iff P K x y

/--
[jei_crossEdge_present](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerInduction.lean)
-/
@[path]
private lemma jei_crossEdge_present_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {x y : P.V}
-- given
  (hadjG : P.G.Adj x y)
  (hnotK : ¬ K.Adj x y) :
-- imply
  crossEdge s(P.emb x, P.emb y) ∈ (regionGraph (jei_pushGraph P K)).edgeSet := by
-- proof
  apply StatMech.Lattice.jei_crossEdge_present P K hadjG hnotK

/--
[jei_dualCount_eq_faceCount_of_sync](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerInduction.lean)
-/
@[path]
private lemma jei_dualCount_eq_faceCount_of_sync_eq
  {P : PlanarZ2Subgraph}
-- given
  (hsync : jei_BridgeCycleDual P) :
-- imply
  ∀ (K : SimpleGraph P.V), K ≤ P.G → Nat.card (regionGraph (jei_pushGraph P K)).ConnectedComponent = faceCount K := by
-- proof
  apply StatMech.Lattice.jei_dualCount_eq_faceCount_of_sync P hsync

/--
[jei_dualEulerCount_of_sync](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerInduction.lean)
-/
@[path]
private lemma jei_dualEulerCount_of_sync_eq
  {P : PlanarZ2Subgraph}
-- given
  (hsync : jei_BridgeCycleDual P) :
-- imply
  jcr_DualEulerCount P := by
-- proof
  apply StatMech.Lattice.jei_dualEulerCount_of_sync P hsync

/--
[jei_planarCutCycleDuality_of_sync](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerInduction.lean)
-/
@[path]
private lemma jei_planarCutCycleDuality_of_sync_eq
  {P : PlanarZ2Subgraph}
-- given
  (hsync : jei_BridgeCycleDual P) :
-- imply
  jsf_PlanarCutCycleDuality P := by
-- proof
  apply StatMech.Lattice.jei_planarCutCycleDuality_of_sync P hsync

/--
[jei_discreteJordan_of_sync](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerInduction.lean)
-/
@[path]
private lemma jei_discreteJordan_of_sync_eq
  {P : PlanarZ2Subgraph}
-- given
  (hsync : jei_BridgeCycleDual P) :
-- imply
  DiscreteJordanSeparation P := by
-- proof
  apply StatMech.Lattice.jei_discreteJordan_of_sync P hsync

/--
[jei_bridgeCycleDual_of_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerInduction.lean)
-/
@[path]
private lemma jei_bridgeCycleDual_of_bot_eq
  {P : PlanarZ2Subgraph}
-- given
  (hG : P.G = ⊥) :
-- imply
  jei_BridgeCycleDual P := by
-- proof
  apply StatMech.Lattice.jei_bridgeCycleDual_of_bot hG

/--
[jei_dualEulerCount_of_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerInduction.lean)
-/
@[path]
private lemma jei_dualEulerCount_of_bot_eq
  {P : PlanarZ2Subgraph}
-- given
  (hG : P.G = ⊥) :
-- imply
  jcr_DualEulerCount P := by
-- proof
  apply StatMech.Lattice.jei_dualEulerCount_of_bot hG


-- created on 2026-10-23
