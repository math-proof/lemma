import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanCrossingCount.Part7
open SimpleGraph Set StatMech StatMech.Lattice


/--
[jcx_isEven_of_isCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_isEven_of_isCycles_eq
  [Empty.Finite V]
  {K : SimpleGraph V}
-- given
  (hcyc : K.IsCycles) :
-- imply
  jcx_IsEven K := by
-- proof
  apply StatMech.Lattice.jcx_isEven_of_isCycles hcyc

/--
[jcx_cycle_neighborCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_cycle_neighborCard_eq
  [Empty.Finite V]
  {K : SimpleGraph V}
  {v : V}
  {p : K.Walk v v}
  {u : V}
-- given
  (hp : p.IsCycle) :
-- imply
  Nat.card (p.toSubgraph.spanningCoe.neighborSet u) = 0 ∨ Nat.card (p.toSubgraph.spanningCoe.neighborSet u) = 2 := by
-- proof
  apply StatMech.Lattice.jcx_cycle_neighborCard p hp u

/--
[jcx_neighborSet_deleteCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_neighborSet_deleteCycle_eq
  [DecidableEq V]
  {K : SimpleGraph V}
  {v : V}
  {p : K.Walk v v}
  {u : V} :
-- imply
  (K.deleteEdges p.toSubgraph.edgeSet).neighborSet u = K.neighborSet u \ p.toSubgraph.spanningCoe.neighborSet u := by
-- proof
  apply StatMech.Lattice.jcx_neighborSet_deleteCycle K p u

/--
[jcx_isEven_deleteCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_isEven_deleteCycle_eq
  [Empty.Finite V]
  [DecidableEq V]
  {K : SimpleGraph V}
  {v : V}
  {p : K.Walk v v}
-- given
  (hev : jcx_IsEven K)
  (hp : p.IsCycle) :
-- imply
  jcx_IsEven (K.deleteEdges p.toSubgraph.edgeSet) := by
-- proof
  apply StatMech.Lattice.jcx_isEven_deleteCycle hev p hp

/--
[jcx_pushGraph_closedContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_pushGraph_closedContour_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  [DecidableRel K.Adj]
-- given
  (hKle : K ≤ P.G)
  (hev : jcx_IsEven K) :
-- imply
  jce_ClosedContour (jei_pushGraph P K).edgeSet := by
-- proof
  apply StatMech.Lattice.jcx_pushGraph_closedContour P K hKle hev

/--
[jcx_addWalk_tc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_addWalk_tc_eq
  {P : PlanarZ2Subgraph} :
-- imply
  ∀ {x y : P.V} (q : P.G.Walk x y) (H : SimpleGraph P.V), q.IsPath → (∀ u ∈ q.support, u ≠ y → ∀ w, ¬ H.Adj u w) → jic_tc P (H ⊔ q.toSubgraph.spanningCoe) = jic_tc P H := by
-- proof
  apply StatMech.Lattice.jcx_addWalk_tc P

/--
[jcx_walk_spanningCoe_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_walk_spanningCoe_reachable_eq
  {G : SimpleGraph V}
  {x y : V}
  {q : G.Walk x y} :
-- imply
  q.toSubgraph.spanningCoe.Reachable x y := by
-- proof
  apply StatMech.Lattice.jcx_walk_spanningCoe_reachable q

/--
[jcx_tc_deleteCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_tc_deleteCycle_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  [DecidableRel K.Adj]
  {v : P.V}
  {p : K.Walk v v}
-- given
  (hKle : K ≤ P.G)
  (hev : jcx_IsEven K)
  (hp : p.IsCycle)
  (hiso : ∀ u ∈ p.support, u ≠ v → ∀ w, ¬ (K.deleteEdges p.toSubgraph.edgeSet).Adj u w) :
-- imply
  jic_tc P K = jic_tc P (K.deleteEdges p.toSubgraph.edgeSet) + 1 := by
-- proof
  apply StatMech.Lattice.jcx_tc_deleteCycle P K hKle hev p hp hiso

/--
[jcx_addWalk_faceCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_addWalk_faceCount_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V} :
-- imply
  ∀ {x y : V} (q : G.Walk x y) (H : SimpleGraph V), q.IsPath → (∀ u ∈ q.support, u ≠ y → ∀ w, ¬ H.Adj u w) → faceCount (H ⊔ q.toSubgraph.spanningCoe) = faceCount H ∧ (∀ u ∈ q.support, (H ⊔ q.toSubgraph.spanningCoe).Reachable x u) := by
-- proof
  apply StatMech.Lattice.jcx_addWalk_faceCount

/--
[jcx_faceCount_deleteCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_faceCount_deleteCycle_eq
  [Empty.Finite V]
  [DecidableEq V]
  {K : SimpleGraph V}
  [LocallyFinite K]
  {v : V}
  {p : K.Walk v v}
-- given
  (hp : p.IsCycle)
  (hiso : ∀ u ∈ p.support, u ≠ v → ∀ w, ¬ (K.deleteEdges p.toSubgraph.edgeSet).Adj u w) :
-- imply
  faceCount (K.deleteEdges p.toSubgraph.edgeSet) + 1 = faceCount K := by
-- proof
  apply StatMech.Lattice.jcx_faceCount_deleteCycle K p hp hiso

/--
[jcx_tc_eq_faceCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_tc_eq_faceCount_eq
  {P : PlanarZ2Subgraph} :
-- imply
  ∀ {K : SimpleGraph P.V}, jcx_IsEvenPeelable K → K ≤ P.G → jic_tc P K = faceCount K := by
-- proof
  apply StatMech.Lattice.jcx_tc_eq_faceCount P

/--
[jcx_total_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_total_count_eq
  {P : PlanarZ2Subgraph}
-- given
  (hpe : jcx_IsEvenPeelable P.G) :
-- imply
  Nat.card (whb_faceRegion (imageGraph P)).ConnectedComponent = faceCount P.G := by
-- proof
  apply StatMech.Lattice.jcx_total_count P hpe

/--
[jcx_faithfulRegionCount_eq_nullity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_faithfulRegionCount_eq_nullity_eq
  {P : PlanarZ2Subgraph}
-- given
  (hpe : jcx_IsEvenPeelable P.G) :
-- imply
  whc_faithfulRegionCount P = nullity P.G := by
-- proof
  apply StatMech.Lattice.jcx_faithfulRegionCount_eq_nullity P hpe

/--
[jcx_faithfulDiscreteJordan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_faithfulDiscreteJordan_eq
  {P : PlanarZ2Subgraph}
-- given
  (hpe : jcx_IsEvenPeelable P.G) :
-- imply
  whc_FaithfulDiscreteJordan P := by
-- proof
  apply StatMech.Lattice.jcx_faithfulDiscreteJordan P hpe

/--
[jcx_cycleVerts_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_cycleVerts_isolated_eq
  [Empty.Finite V]
  [DecidableEq V]
  {K : SimpleGraph V}
  [LocallyFinite K]
  {v : V}
  {p : K.Walk v v}
-- given
  (hcyc : K.IsCycles)
  (hp : p.IsCycle) :
-- imply
  ∀ u ∈ p.support, ∀ w, ¬ (K.deleteEdges p.toSubgraph.edgeSet).Adj u w := by
-- proof
  apply StatMech.Lattice.jcx_cycleVerts_isolated hcyc p hp

/--
[jcx_isEvenPeelable_of_isCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_isEvenPeelable_of_isCycles_eq
  [Empty.Finite V]
  [DecidableEq V]
  {K : SimpleGraph V}
-- given
  (hcyc : K.IsCycles) :
-- imply
  jcx_IsEvenPeelable K := by
-- proof
  apply StatMech.Lattice.jcx_isEvenPeelable_of_isCycles K hcyc

/--
[jcx_cross_emb_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_cross_emb_inj_eq :
-- imply
  Function.Injective jcx_cross_emb := by
-- proof
  apply StatMech.Lattice.jcx_cross_emb_inj

/--
[jcx_cross_G_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_cross_G_adj_eq
  {i j : Fin 7} :
-- imply
  jcx_cross_G.Adj i j ↔ jcx_cross_rel i j := by
-- proof
  apply StatMech.Lattice.jcx_cross_G_adj i j

/--
[jcx_cross_isSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_cross_isSub_eq :
-- imply
  ∀ ⦃i j : Fin 7⦄, jcx_cross_G.Adj i j → (hypercubicLattice 2).Adj (jcx_cross_emb i) (jcx_cross_emb j) := by
-- proof
  apply StatMech.Lattice.jcx_cross_isSub

/--
[jcx_cross_deg2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_cross_deg2_eq :
-- imply
  jcx_cross_G.neighborSet 2 = {1, 3, 4, 6} := by
-- proof
  apply StatMech.Lattice.jcx_cross_deg2

/--
[jcx_cross_not_isCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_cross_not_isCycles_eq :
-- imply
  ¬ jcx_cross_G.IsCycles := by
-- proof
  apply StatMech.Lattice.jcx_cross_not_isCycles

/--
[jcx_cross_isEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_cross_isEven_eq :
-- imply
  jcx_IsEven jcx_cross_G := by
-- proof
  apply StatMech.Lattice.jcx_cross_isEven

/--
[jcx_cross_cycB_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_cross_cycB_isCycle_eq :
-- imply
  jcx_cross_cycB.IsCycle := by
-- proof
  apply StatMech.Lattice.jcx_cross_cycB_isCycle

/--
[jcx_cross_A_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_cross_A_adj_eq
  {i j : Fin 7} :
-- imply
  jcx_cross_A.Adj i j ↔ jcx_cross_A_rel i j := by
-- proof
  apply StatMech.Lattice.jcx_cross_A_adj i j

/--
[jcx_cross_delete_eq_A](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_cross_delete_eq_A_eq :
-- imply
  jcx_cross_G.deleteEdges jcx_cross_cycB.toSubgraph.edgeSet = jcx_cross_A := by
-- proof
  apply StatMech.Lattice.jcx_cross_delete_eq_A

/--
[jcx_cross_cycB_iso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_cross_cycB_iso_eq :
-- imply
  ∀ u ∈ jcx_cross_cycB.support, u ≠ 2 → ∀ w, ¬ (jcx_cross_G.deleteEdges jcx_cross_cycB.toSubgraph.edgeSet).Adj u w := by
-- proof
  apply StatMech.Lattice.jcx_cross_cycB_iso

/--
[jcx_cross_A_isCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_cross_A_isCycles_eq :
-- imply
  jcx_cross_A.IsCycles := by
-- proof
  apply StatMech.Lattice.jcx_cross_A_isCycles

/--
[jcx_cross_isEvenPeelable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_cross_isEvenPeelable_eq :
-- imply
  jcx_IsEvenPeelable jcx_cross_G := by
-- proof
  apply StatMech.Lattice.jcx_cross_isEvenPeelable

/--
[jcx_faithfulDiscreteJordan_twoSquaresCorner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean)
-/
@[path]
private lemma jcx_faithfulDiscreteJordan_twoSquaresCorner_eq :
-- imply
  whc_FaithfulDiscreteJordan jcx_cross_P := by
-- proof
  apply StatMech.Lattice.jcx_faithfulDiscreteJordan_twoSquaresCorner


-- created on 2026-10-23
