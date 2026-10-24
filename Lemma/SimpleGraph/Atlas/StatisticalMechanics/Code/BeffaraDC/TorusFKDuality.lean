import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.BeffaraDC.TorusFKDuality
open SimpleGraph Set StatMech StatMech.BeffaraDC


/--
[torusQuarterTurnEdge_mem_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusFKDuality.lean)
-/
@[path]
private lemma torusQuarterTurnEdge_mem_edgeFinset_eq
  {L : ℕ}
  [Fact (2 < L)]
  {e : Sym2 (ZMod L × ZMod L)} :
-- imply
  e ∈ (onsTorusGraph L).edgeFinset ↔ torusQuarterTurnEdge L e ∈ (onsTorusGraph L).edgeFinset := by
-- proof
  apply StatMech.BeffaraDC.torusQuarterTurnEdge_mem_edgeFinset L e

/--
[torus_dual_openCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusFKDuality.lean)
-/
@[path]
private lemma torus_dual_openCount_eq
  {L : ℕ}
  [Fact (2 < L)]
  {ω : ConfigSpace (Sym2 (ZMod L × ZMod L))} :
-- imply
  FK.openCount (onsTorusGraph L) (torusDualConfig L ω) = (onsTorusGraph L).edgeFinset.card - FK.openCount (onsTorusGraph L) ω := by
-- proof
  apply StatMech.BeffaraDC.torus_dual_openCount L ω

/--
[torus_openSub_dualConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusFKDuality.lean)
-/
@[path]
private lemma torus_openSub_dualConfig_eq
  {L : ℕ}
  [Fact (2 < L)]
  {ω : ConfigSpace (Sym2 (ZMod L × ZMod L))} :
-- imply
  FK.openSub (onsTorusGraph L) (torusDualConfig L ω) = torusDualCutGraph L (FK.openSub (onsTorusGraph L) ω) := by
-- proof
  apply StatMech.BeffaraDC.torus_openSub_dualConfig L ω

/--
[torus_numClusters_dualConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusFKDuality.lean)
-/
@[path]
private lemma torus_numClusters_dualConfig_eq
  {L : ℕ}
  [Fact (2 < L)]
  {ω : ConfigSpace (Sym2 (ZMod L × ZMod L))} :
-- imply
  FK.numClusters (onsTorusGraph L) (torusDualConfig L ω) = torusGeometricFaceCount L (FK.openSub (onsTorusGraph L) ω) := by
-- proof
  apply StatMech.BeffaraDC.torus_numClusters_dualConfig L ω

/--
[torus_openSub_edge_ncard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusFKDuality.lean)
-/
@[path]
private lemma torus_openSub_edge_ncard_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  (FK.openSub G ω).edgeSet.ncard = FK.openCount G ω := by
-- proof
  apply StatMech.BeffaraDC.torus_openSub_edge_ncard G ω

/--
[torus_primalWeight_openSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusFKDuality.lean)
-/
@[path]
private lemma torus_primalWeight_openSub_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 (ZMod L × ZMod L))} :
-- imply
  torusPrimalWeight L p q (FK.openSub (onsTorusGraph L) ω) = FK.fkWeight (onsTorusGraph L) p q ω := by
-- proof
  apply StatMech.BeffaraDC.torus_primalWeight_openSub L p q ω

/--
[torus_dualWeight_openSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusFKDuality.lean)
-/
@[path]
private lemma torus_dualWeight_openSub_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 (ZMod L × ZMod L))} :
-- imply
  torusDualWeight L p q (FK.openSub (onsTorusGraph L) ω) = FK.fkWeight (onsTorusGraph L) p q (torusDualConfig L ω) := by
-- proof
  apply StatMech.BeffaraDC.torus_dualWeight_openSub L p q ω

/--
[torusPrimalWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusFKDuality.lean)
-/
@[path]
private lemma torusPrimalWeight_pos_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (ZMod L × ZMod L)}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < torusPrimalWeight L p q K := by
-- proof
  apply StatMech.BeffaraDC.torusPrimalWeight_pos L K hp hp1 hq

/--
[torusDualWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusFKDuality.lean)
-/
@[path]
private lemma torusDualWeight_pos_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (ZMod L × ZMod L)}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < torusDualWeight L p q K := by
-- proof
  apply StatMech.BeffaraDC.torusDualWeight_pos L K hp hp1 hq

/--
[torus_subgraph_edgeCount_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusFKDuality.lean)
-/
@[path]
private lemma torus_subgraph_edgeCount_le_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (ZMod L × ZMod L)}
-- given
  (hK : K ≤ onsTorusGraph L) :
-- imply
  K.edgeSet.ncard ≤ (onsTorusGraph L).edgeFinset.card := by
-- proof
  apply StatMech.BeffaraDC.torus_subgraph_edgeCount_le L K hK

/--
[torus_clusterEuler_signed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusFKDuality.lean)
-/
@[path]
private lemma torus_clusterEuler_signed_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (ZMod L × ZMod L)} :
-- imply
  ((K.edgeSet.ncard + Nat.card K.ConnectedComponent + 1 : ℕ) : ℤ) = ((Nat.card (ZMod L × ZMod L) + torusGeometricFaceCount L K : ℕ) : ℤ) + torusGeometricDefect L K := by
-- proof
  apply StatMech.BeffaraDC.torus_clusterEuler_signed L K

/--
[torus_weight_duality_signed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusFKDuality.lean)
-/
@[path]
private lemma torus_weight_duality_signed_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (ZMod L × ZMod L)}
  {p q : ℝ}
-- given
  (hK : K ≤ onsTorusGraph L)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  torusPrimalWeight L p q K * q ^ ((onsTorusGraph L).edgeFinset.card + 1) = (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card * q ^ Nat.card (ZMod L × ZMod L) * torusDualWeight L (dualParam p q) q K * q ^ torusGeometricDefect L K := by
-- proof
  apply StatMech.BeffaraDC.torus_weight_duality_signed L K hK hp hp1 hq

/--
[torus_fkWeight_duality_signed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusFKDuality.lean)
-/
@[path]
private lemma torus_fkWeight_duality_signed_eq
  {L : ℕ}
  [Fact (2 < L)]
  {ω : ConfigSpace (Sym2 (ZMod L × ZMod L))}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  FK.fkWeight (onsTorusGraph L) p q ω * q ^ ((onsTorusGraph L).edgeFinset.card + 1) = (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card * q ^ Nat.card (ZMod L × ZMod L) * FK.fkWeight (onsTorusGraph L) (dualParam p q) q (torusDualConfig L ω) * q ^ torusGeometricDefect L (FK.openSub (onsTorusGraph L) ω) := by
-- proof
  apply StatMech.BeffaraDC.torus_fkWeight_duality_signed L ω hp hp1 hq

/--
[torus_weight_duality_of_defect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusFKDuality.lean)
-/
@[path]
private lemma torus_weight_duality_of_defect_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (ZMod L × ZMod L)}
  {p q : ℝ}
  {δ : ℕ}
-- given
  (hK : K ≤ onsTorusGraph L)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hδ : torusGeometricDefect L K = δ) :
-- imply
  torusPrimalWeight L p q K * q ^ ((onsTorusGraph L).edgeFinset.card + 1) = (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card * q ^ Nat.card (ZMod L × ZMod L) * torusDualWeight L (dualParam p q) q K * q ^ δ := by
-- proof
  apply StatMech.BeffaraDC.torus_weight_duality_of_defect L K hK hp hp1 hq δ hδ

/--
[torus_weight_q_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusFKDuality.lean)
-/
@[path]
private lemma torus_weight_q_sandwich_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (ZMod L × ZMod L)}
  {p q : ℝ}
-- given
  (hclass : TorusDefectClassified L)
  (hK : K ≤ onsTorusGraph L)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq1 : 1 ≤ q) :
-- imply
  let primal := torusPrimalWeight L p q K * q ^ ((onsTorusGraph L).edgeFinset.card + 1) let dual := (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card * q ^ Nat.card (ZMod L × ZMod L) * q * torusDualWeight L (dualParam p q) q K primal ≤ q * dual ∧ dual ≤ q * primal := by
-- proof
  apply StatMech.BeffaraDC.torus_weight_q_sandwich L hclass K hK hp hp1 hq1

/--
[torus_normalized_event_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusFKDuality.lean)
-/
@[path]
private lemma torus_normalized_event_comparison_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
  {A : Finset (ConfigSpace (Sym2 (ZMod L × ZMod L)))}
-- given
  (hclass : TorusDefectClassified L)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq1 : 1 ≤ q) :
-- imply
  let w := fun ω : ConfigSpace (Sym2 (ZMod L × ZMod L)) => torusPrimalWeight L p q (FK.openSub (onsTorusGraph L) ω) * q ^ ((onsTorusGraph L).edgeFinset.card + 1) let w' := fun ω : ConfigSpace (Sym2 (ZMod L × ZMod L)) => (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card * q ^ Nat.card (ZMod L × ZMod L) * q * torusDualWeight L (dualParam p q) q (FK.openSub (onsTorusGraph L) ω) (∑ ω ∈ A, w ω) / (∑ ω, w ω) ≤ q ^ 2 * ((∑ ω ∈ A, w' ω) / (∑ ω, w' ω)) := by
-- proof
  apply StatMech.BeffaraDC.torus_normalized_event_comparison L hclass hp hp1 hq1 A


-- created on 2026-10-23
