import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.JordanBridgeCycle
open SimpleGraph Set StatMech StatMech.Lattice


/--
[jbc_rot90Inv_rot90Fun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_rot90Inv_rot90Fun_eq
  {a : Site 2} :
-- imply
  rot90Inv (rot90Fun a) = a := by
-- proof
  apply StatMech.Lattice.jbc_rot90Inv_rot90Fun a

/--
[jbc_rot90Fun_rot90Inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_rot90Fun_rot90Inv_eq
  {a : Site 2} :
-- imply
  rot90Fun (rot90Inv a) = a := by
-- proof
  apply StatMech.Lattice.jbc_rot90Fun_rot90Inv a

/--
[jbc_crossEdge_symm_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_crossEdge_symm_pair_eq
  {f g : Site 2} :
-- imply
  crossEdge.symm s(f, g) = s(rot90Inv f, rot90Inv g) := by
-- proof
  apply StatMech.Lattice.jbc_crossEdge_symm_pair f g

/--
[jbc_crossEdge_symm_rot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_crossEdge_symm_rot_eq
  {a b : Site 2} :
-- imply
  crossEdge.symm s(rot90Fun a, rot90Fun b) = s(a, b) := by
-- proof
  apply StatMech.Lattice.jbc_crossEdge_symm_rot a b

/--
[jbc_latticeMinusEdges_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_latticeMinusEdges_adj_eq
  {H : SimpleGraph (Site 2)}
  {a b : Site 2} :
-- imply
  (jbc_latticeMinusEdges H).Adj a b ↔ (hypercubicLattice 2).Adj a b ∧ s(a, b) ∉ H.edgeSet := by
-- proof
  apply StatMech.Lattice.jbc_latticeMinusEdges_adj H a b

/--
[jbc_regionGraph_rot_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_regionGraph_rot_adj_eq
  {H : SimpleGraph (Site 2)}
  {a b : Site 2} :
-- imply
  (regionGraph H).Adj (rot90Fun a) (rot90Fun b) ↔ (jbc_latticeMinusEdges H).Adj a b := by
-- proof
  apply StatMech.Lattice.jbc_regionGraph_rot_adj H a b

/--
[jbc_rotIso_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_rotIso_apply_eq
  {H : SimpleGraph (Site 2)}
  {a : Site 2} :
-- imply
  jbc_rotIso H a = rot90Fun a := by
-- proof
  apply StatMech.Lattice.jbc_rotIso_apply H a

/--
[jbc_regionGraph_reachable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_regionGraph_reachable_iff_eq
  {H : SimpleGraph (Site 2)}
  {a b : Site 2} :
-- imply
  (regionGraph H).Reachable (rot90Fun a) (rot90Fun b) ↔ (jbc_latticeMinusEdges H).Reachable a b := by
-- proof
  apply StatMech.Lattice.jbc_regionGraph_reachable_iff H a b

/--
[jbc_deleteRegion_le_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_deleteRegion_le_lattice_eq
  {H : SimpleGraph (Site 2)}
  {e : Set (Sym2 (Site 2))} :
-- imply
  (regionGraph H).deleteEdges e ≤ hypercubicLattice 2 := by
-- proof
  apply StatMech.Lattice.jbc_deleteRegion_le_lattice H e

/--
[jbc_deleteRegion_eq_pushSup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_deleteRegion_eq_pushSup_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {x y : P.V}
-- given
  (hne : x ≠ y) :
-- imply
  (regionGraph (jei_pushGraph P K)).deleteEdges {crossEdge s(P.emb x, P.emb y)} = regionGraph (jei_pushGraph P (K ⊔ edge x y)) := by
-- proof
  apply StatMech.Lattice.jbc_deleteRegion_eq_pushSup P K hne

/--
[jbc_dualSide_iff_primalAvoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_dualSide_iff_primalAvoid_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {x y : P.V}
-- given
  (hne : x ≠ y) :
-- imply
  ((regionGraph (jei_pushGraph P K)).deleteEdges {crossEdge s(P.emb x, P.emb y)}).Reachable (rot90Fun (P.emb x)) (rot90Fun (P.emb y)) ↔ (jbc_latticeMinusEdges (jei_pushGraph P (K ⊔ edge x y))).Reachable (P.emb x) (P.emb y) := by
-- proof
  apply StatMech.Lattice.jbc_dualSide_iff_primalAvoid P K hne

/--
[jbc_bridgeCycleDual_of_reduced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_bridgeCycleDual_of_reduced_eq
  {P : PlanarZ2Subgraph}
-- given
  (h : jbc_ReducedBridgeCycle P) :
-- imply
  jei_BridgeCycleDual P := by
-- proof
  apply StatMech.Lattice.jbc_bridgeCycleDual_of_reduced P h

/--
[jbc_discreteJordan_of_reduced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_discreteJordan_of_reduced_eq
  {P : PlanarZ2Subgraph}
-- given
  (h : jbc_ReducedBridgeCycle P) :
-- imply
  DiscreteJordanSeparation P := by
-- proof
  apply StatMech.Lattice.jbc_discreteJordan_of_reduced P h

/--
[jbc_reducedBridgeCycle_of_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_reducedBridgeCycle_of_bot_eq
  {P : PlanarZ2Subgraph}
-- given
  (hG : P.G = ⊥) :
-- imply
  jbc_ReducedBridgeCycle P := by
-- proof
  apply StatMech.Lattice.jbc_reducedBridgeCycle_of_bot hG

/--
[jbc_discreteJordan_of_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_discreteJordan_of_bot_eq
  {P : PlanarZ2Subgraph}
-- given
  (hG : P.G = ⊥) :
-- imply
  DiscreteJordanSeparation P := by
-- proof
  apply StatMech.Lattice.jbc_discreteJordan_of_bot hG

/--
[jbc_reduced_of_directions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_reduced_of_directions_eq
  {P : PlanarZ2Subgraph}
-- given
  (hcyc : jbc_CycleDirection P)
  (hbr : jbc_BridgeDirection P) :
-- imply
  jbc_ReducedBridgeCycle P := by
-- proof
  apply StatMech.Lattice.jbc_reduced_of_directions P hcyc hbr

/--
[jbc_csq_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_csq_inj_eq :
-- imply
  Function.Injective jbc_csq := by
-- proof
  apply StatMech.Lattice.jbc_csq_inj

/--
[jbc_csq_y](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_csq_y_eq
  {i : Fin 4} :
-- imply
  (jbc_csq i) 1 = 0 ∨ (jbc_csq i) 1 = 1 := by
-- proof
  apply StatMech.Lattice.jbc_csq_y i

/--
[jbc_cyc4_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_cyc4_adj_eq
  {i j : Fin 4} :
-- imply
  jbc_cyc4.Adj i j ↔ jbc_cyc4Rel i j := by
-- proof
  apply StatMech.Lattice.jbc_cyc4_adj i j

/--
[jbc_csq_isSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_csq_isSub_eq :
-- imply
  ∀ ⦃i j : Fin 4⦄, jbc_cyc4.Adj i j → (hypercubicLattice 2).Adj (jbc_csq i) (jbc_csq j) := by
-- proof
  apply StatMech.Lattice.jbc_csq_isSub

/--
[jbc_path3_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_path3_adj_eq
  {i j : Fin 4} :
-- imply
  jbc_path3.Adj i j ↔ jbc_path3Rel i j := by
-- proof
  apply StatMech.Lattice.jbc_path3_adj i j

/--
[jbc_path3_le_cyc4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_path3_le_cyc4_eq :
-- imply
  jbc_path3 ≤ jbc_cyc4 := by
-- proof
  apply StatMech.Lattice.jbc_path3_le_cyc4

/--
[jbc_v0_ne_v1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_v0_ne_v1_eq :
-- imply
  jbc_v0 ≠ jbc_v1 := by
-- proof
  apply StatMech.Lattice.jbc_v0_ne_v1

/--
[jbc_path3_sup_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_path3_sup_edge_eq :
-- imply
  jbc_path3 ⊔ edge jbc_v0 jbc_v1 = jbc_cyc4 := by
-- proof
  apply StatMech.Lattice.jbc_path3_sup_edge

/--
[jbc_path3_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_path3_reach_eq :
-- imply
  jbc_path3.Reachable jbc_v0 jbc_v1 := by
-- proof
  apply StatMech.Lattice.jbc_path3_reach

/--
[jbc_not_pushed_ym1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_not_pushed_ym1_eq
  {a b : Site 2}
-- given
  (ha : a 1 = -1) :
-- imply
  ¬ (jei_pushGraph jbc_Pce jbc_cyc4).Adj a b := by
-- proof
  apply StatMech.Lattice.jbc_not_pushed_ym1 ha

/--
[jbc_not_pushed_ym1'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_not_pushed_ym1'_eq
  {a b : Site 2}
-- given
  (hb : b 1 = -1) :
-- imply
  ¬ (jei_pushGraph jbc_Pce jbc_cyc4).Adj a b := by
-- proof
  apply StatMech.Lattice.jbc_not_pushed_ym1' hb

/--
[jbc_latadj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_latadj_eq
  {a b : Site 2}
-- given
  (h : (∑ i, (a i - b i).natAbs) = 1) :
-- imply
  (hypercubicLattice 2).Adj a b := by
-- proof
  apply StatMech.Lattice.jbc_latadj h

/--
[jbc_around_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_around_reach_eq :
-- imply
  (jbc_latticeMinusEdges (jei_pushGraph jbc_Pce jbc_cyc4)).Reachable ![0, 0] ![1, 0] := by
-- proof
  apply StatMech.Lattice.jbc_around_reach

/--
[jbc_Pce_emb0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_Pce_emb0_eq :
-- imply
  jbc_Pce.emb jbc_v0 = ![0, 0] := by
-- proof
  apply StatMech.Lattice.jbc_Pce_emb0

/--
[jbc_Pce_emb1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_Pce_emb1_eq :
-- imply
  jbc_Pce.emb jbc_v1 = ![1, 0] := by
-- proof
  apply StatMech.Lattice.jbc_Pce_emb1

/--
[jbc_Pce_Gadj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_Pce_Gadj_eq :
-- imply
  jbc_Pce.G.Adj jbc_v0 jbc_v1 := by
-- proof
  apply StatMech.Lattice.jbc_Pce_Gadj

/--
[jbc_Pce_not_Kadj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_Pce_not_Kadj_eq :
-- imply
  ¬ jbc_path3.Adj jbc_v0 jbc_v1 := by
-- proof
  apply StatMech.Lattice.jbc_Pce_not_Kadj

/--
[jbc_enlarged_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_enlarged_reach_eq :
-- imply
  (jbc_latticeMinusEdges (jei_pushGraph jbc_Pce (jbc_path3 ⊔ edge jbc_v0 jbc_v1))).Reachable (jbc_Pce.emb jbc_v0) (jbc_Pce.emb jbc_v1) := by
-- proof
  apply StatMech.Lattice.jbc_enlarged_reach

/--
[jbc_jei_bridgeCycleDual_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_jei_bridgeCycleDual_false_eq :
-- imply
  ¬ jei_BridgeCycleDual jbc_Pce := by
-- proof
  apply StatMech.Lattice.jbc_jei_bridgeCycleDual_false

/--
[jbc_reducedBridgeCycle_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_reducedBridgeCycle_false_eq :
-- imply
  ¬ jbc_ReducedBridgeCycle jbc_Pce := by
-- proof
  apply StatMech.Lattice.jbc_reducedBridgeCycle_false

/--
[jbc_cycleDirection_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_cycleDirection_false_eq :
-- imply
  ¬ jbc_CycleDirection jbc_Pce := by
-- proof
  apply StatMech.Lattice.jbc_cycleDirection_false

/--
[jbc_crossSymm_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_crossSymm_pair_eq
  {f g : Site 2} :
-- imply
  crossEdge.symm s(f, g) = s(rot90Inv f, rot90Inv g) := by
-- proof
  apply StatMech.Lattice.jbc_crossSymm_pair f g

/--
[jbc_not_contour_ym1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_not_contour_ym1_eq
  {f g : Site 2}
-- given
  (h : (rot90Inv f) 1 = -1) :
-- imply
  crossEdge.symm s(f, g) ∉ (jei_pushGraph jbc_Pce jbc_cyc4).edgeSet := by
-- proof
  apply StatMech.Lattice.jbc_not_contour_ym1 h

/--
[jbc_not_contour_ym1'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_not_contour_ym1'_eq
  {f g : Site 2}
-- given
  (h : (rot90Inv g) 1 = -1) :
-- imply
  crossEdge.symm s(f, g) ∉ (jei_pushGraph jbc_Pce jbc_cyc4).edgeSet := by
-- proof
  apply StatMech.Lattice.jbc_not_contour_ym1' h

/--
[jbc_vne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_vne_eq
  {a b : Site 2}
-- given
  (h0 : a 0 ≠ b 0 ∨ a 1 ≠ b 1) :
-- imply
  a ≠ b := by
-- proof
  apply StatMech.Lattice.jbc_vne h0

/--
[jbc_DR_true_direct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_DR_true_direct_eq :
-- imply
  (regionGraph (jei_pushGraph jbc_Pce jbc_cyc4)).Reachable (rot90Fun (jbc_csq 0)) (rot90Fun (jbc_csq 1)) := by
-- proof
  apply StatMech.Lattice.jbc_DR_true_direct

/--
[jbc_jei_bridgeCycleDual_false_direct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean)
-/
@[path]
private lemma jbc_jei_bridgeCycleDual_false_direct_eq :
-- imply
  ¬ jei_BridgeCycleDual jbc_Pce := by
-- proof
  apply StatMech.Lattice.jbc_jei_bridgeCycleDual_false_direct


-- created on 2026-10-23
