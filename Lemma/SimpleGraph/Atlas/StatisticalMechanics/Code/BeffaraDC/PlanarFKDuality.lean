import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
open Finset SimpleGraph Set StatMech StatMech.BeffaraDC


/--
[pfdClosedDual_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean)
-/
@[path]
private lemma pfdClosedDual_adj_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {C D : kwg_Face P} :
-- imply
  (pfdClosedDual P K).Adj C D ↔ C ≠ D ∧ ∃ e : kwg_Edge P, e.1 ∉ K.edgeSet ∧ kwg_dualEnds P e = s(C, D) := by
-- proof
  apply StatMech.BeffaraDC.pfdClosedDual_adj P K C D

/--
[pfd_faceStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean)
-/
@[path]
private lemma pfd_faceStep_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {f g : Site 2}
-- given
  (hfg : (whb_faceRegion (jei_pushGraph P K)).Adj f g) :
-- imply
  (pfdClosedDual P K).Reachable (pfdFace P f) (pfdFace P g) := by
-- proof
  apply StatMech.BeffaraDC.pfd_faceStep P K hfg

/--
[pfd_regionReachable_to_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean)
-/
@[path]
private lemma pfd_regionReachable_to_dual_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {f g : Site 2}
-- given
  (hfg : (whb_faceRegion (jei_pushGraph P K)).Reachable f g) :
-- imply
  (pfdClosedDual P K).Reachable (pfdFace P f) (pfdFace P g) := by
-- proof
  apply StatMech.BeffaraDC.pfd_regionReachable_to_dual P K hfg

/--
[pfd_embeddedEdge_not_mem_push](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean)
-/
@[path]
private lemma pfd_embeddedEdge_not_mem_push_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {e : kwg_Edge P}
-- given
  (heK : e.1 ∉ K.edgeSet) :
-- imply
  kwg_embeddedEdge P e ∉ (jei_pushGraph P K).edgeSet := by
-- proof
  apply StatMech.BeffaraDC.pfd_embeddedEdge_not_mem_push P K e heK

/--
[pfd_ambientFace_le_openFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean)
-/
@[path]
private lemma pfd_ambientFace_le_openFace_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
-- given
  (hKP : K ≤ P.G) :
-- imply
  whb_faceRegion (imageGraph P) ≤ whb_faceRegion (jei_pushGraph P K) := by
-- proof
  apply StatMech.BeffaraDC.pfd_ambientFace_le_openFace P K hKP

/--
[pfd_dualAdj_to_regionReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean)
-/
@[path]
private lemma pfd_dualAdj_to_regionReachable_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {f g : Site 2}
-- given
  (hKP : K ≤ P.G)
  (hfg : (pfdClosedDual P K).Adj (pfdFace P f) (pfdFace P g)) :
-- imply
  (whb_faceRegion (jei_pushGraph P K)).Reachable f g := by
-- proof
  apply StatMech.BeffaraDC.pfd_dualAdj_to_regionReachable P K hKP hfg

/--
[pfd_dualWalk_to_regionReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean)
-/
@[path]
private lemma pfd_dualWalk_to_regionReachable_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {C D : kwg_Face P}
  {w : (pfdClosedDual P K).Walk C D}
  {f g : Site 2}
-- given
  (hKP : K ≤ P.G)
  (hf : pfdFace P f = C)
  (hg : pfdFace P g = D) :
-- imply
  (whb_faceRegion (jei_pushGraph P K)).Reachable f g := by
-- proof
  apply StatMech.BeffaraDC.pfd_dualWalk_to_regionReachable P K hKP w hf hg

/--
[pfd_regionReachable_iff_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean)
-/
@[path]
private lemma pfd_regionReachable_iff_dual_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {f g : Site 2}
-- given
  (hKP : K ≤ P.G) :
-- imply
  (whb_faceRegion (jei_pushGraph P K)).Reachable f g ↔ (pfdClosedDual P K).Reachable (pfdFace P f) (pfdFace P g) := by
-- proof
  apply StatMech.BeffaraDC.pfd_regionReachable_iff_dual P K hKP

/--
[pfd_numDualClusters_eq_faceComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean)
-/
@[path]
private lemma pfd_numDualClusters_eq_faceComponents_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
-- given
  (hKP : K ≤ P.G) :
-- imply
  Nat.card (pfdClosedDual P K).ConnectedComponent = Nat.card (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent := by
-- proof
  apply StatMech.BeffaraDC.pfd_numDualClusters_eq_faceComponents P K hKP

/--
[pfdOpenPlanar_imageGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean)
-/
@[path]
private lemma pfdOpenPlanar_imageGraph_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
-- given
  (hKP : K ≤ P.G) :
-- imply
  imageGraph (pfdOpenPlanar P K hKP) = jei_pushGraph P K := by
-- proof
  apply StatMech.BeffaraDC.pfdOpenPlanar_imageGraph P K hKP

/--
[pfdOpenPlanar_graph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean)
-/
@[path]
private lemma pfdOpenPlanar_graph_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
-- given
  (hKP : K ≤ P.G) :
-- imply
  (pfdOpenPlanar P K hKP).G = K := by
-- proof
  apply StatMech.BeffaraDC.pfdOpenPlanar_graph P K hKP

/--
[pfd_numFaceComponents_eq_faceCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean)
-/
@[path]
private lemma pfd_numFaceComponents_eq_faceCount_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
-- given
  (hKP : K ≤ P.G) :
-- imply
  Nat.card (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent = faceCount K := by
-- proof
  apply StatMech.BeffaraDC.pfd_numFaceComponents_eq_faceCount P K hKP

/--
[pfd_numDualClusters_eq_faceCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean)
-/
@[path]
private lemma pfd_numDualClusters_eq_faceCount_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
-- given
  (hKP : K ≤ P.G) :
-- imply
  Nat.card (pfdClosedDual P K).ConnectedComponent = faceCount K := by
-- proof
  apply StatMech.BeffaraDC.pfd_numDualClusters_eq_faceCount P K hKP

/--
[pfd_clusterEuler](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean)
-/
@[path]
private lemma pfd_clusterEuler_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
-- given
  (hKP : K ≤ P.G) :
-- imply
  Nat.card P.V + Nat.card (pfdClosedDual P K).ConnectedComponent = K.edgeSet.ncard + Nat.card K.ConnectedComponent + 1 := by
-- proof
  apply StatMech.BeffaraDC.pfd_clusterEuler P K hKP

/--
[pfd_subgraph_edgeCount_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean)
-/
@[path]
private lemma pfd_subgraph_edgeCount_le_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
-- given
  (hKP : K ≤ P.G) :
-- imply
  K.edgeSet.ncard ≤ P.G.edgeFinset.card := by
-- proof
  apply StatMech.BeffaraDC.pfd_subgraph_edgeCount_le P K hKP

/--
[pfd_weight_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean)
-/
@[path]
private lemma pfd_weight_duality_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {p q : ℝ}
-- given
  (hKP : K ≤ P.G)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  pfdPrimalWeight P p q K * q ^ (P.G.edgeFinset.card + 1) = (p / (1 - dualParam p q)) ^ P.G.edgeFinset.card * q ^ Nat.card P.V * pfdDualWeight P (dualParam p q) q K := by
-- proof
  apply StatMech.BeffaraDC.pfd_weight_duality P K hKP hp hp1 hq

/--
[pfd_openSub_edge_ncard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean)
-/
@[path]
private lemma pfd_openSub_edge_ncard_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  (FK.openSub G omega).edgeSet.ncard = FK.openCount G omega := by
-- proof
  apply StatMech.BeffaraDC.pfd_openSub_edge_ncard G omega

/--
[pfd_primalWeight_openSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean)
-/
@[path]
private lemma pfd_primalWeight_openSub_eq
  {P : PlanarZ2Subgraph}
  {p q : ℝ}
  {omega : ConfigSpace (Sym2 P.V)} :
-- imply
  pfdPrimalWeight P p q (FK.openSub P.G omega) = FK.fkWeight P.G p q omega := by
-- proof
  apply StatMech.BeffaraDC.pfd_primalWeight_openSub P p q omega

/--
[pfd_fkWeight_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean)
-/
@[path]
private lemma pfd_fkWeight_duality_eq
  {P : PlanarZ2Subgraph}
  {omega : ConfigSpace (Sym2 P.V)}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  FK.fkWeight P.G p q omega * q ^ (P.G.edgeFinset.card + 1) = (p / (1 - dualParam p q)) ^ P.G.edgeFinset.card * q ^ Nat.card P.V * pfdDualWeight P (dualParam p q) q (FK.openSub P.G omega) := by
-- proof
  apply StatMech.BeffaraDC.pfd_fkWeight_duality P omega hp hp1 hq

/--
[pfd_dualWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean)
-/
@[path]
private lemma pfd_dualWeight_pos_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < pfdDualWeight P p q K := by
-- proof
  apply StatMech.BeffaraDC.pfd_dualWeight_pos P K hp hp1 hq

/--
[pfd_dualZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean)
-/
@[path]
private lemma pfd_dualZ_pos_eq
  {P : PlanarZ2Subgraph}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < pfdDualZ P p q := by
-- proof
  apply StatMech.BeffaraDC.pfd_dualZ_pos P hp hp1 hq

/--
[pfd_partition_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean)
-/
@[path]
private lemma pfd_partition_duality_eq
  {P : PlanarZ2Subgraph}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  FK.fkZ P.G p q * q ^ (P.G.edgeFinset.card + 1) = (p / (1 - dualParam p q)) ^ P.G.edgeFinset.card * q ^ Nat.card P.V * pfdDualZ P (dualParam p q) q := by
-- proof
  apply StatMech.BeffaraDC.pfd_partition_duality P hp hp1 hq

/--
[pfd_fkProb_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean)
-/
@[path]
private lemma pfd_fkProb_duality_eq
  {P : PlanarZ2Subgraph}
  {omega : ConfigSpace (Sym2 P.V)}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  FK.fkProb P.G p q omega = pfdDualProb P (dualParam p q) q omega := by
-- proof
  apply StatMech.BeffaraDC.pfd_fkProb_duality P omega hp hp1 hq


-- created on 2026-10-23
