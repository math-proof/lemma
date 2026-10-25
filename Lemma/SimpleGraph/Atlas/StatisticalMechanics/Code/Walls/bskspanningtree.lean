import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bskspanningtree.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bsk_exists_spanningTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bskspanningtree.lean)
-/
@[path]
private lemma bsk_exists_spanningTree_eq
  {d : ℕ}
  {G : SimpleGraph V}
-- given
  (h : G.Connected) :
-- imply
  ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree := by
-- proof
  apply StatMech.Walls.bsk_exists_spanningTree G h

/--
[bsk_three_le_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bskspanningtree.lean)
-/
@[path]
private lemma bsk_three_le_degree_eq
  {d : ℕ}
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {v a b c : W}
-- given
  (hab : a ≠ b)
  (hac : a ≠ c)
  (hbc : b ≠ c)
  (ha : G.Adj v a)
  (hb : G.Adj v b)
  (hc : G.Adj v c) :
-- imply
  3 ≤ G.degree v := by
-- proof
  apply StatMech.Walls.bsk_three_le_degree G hab hac hbc ha hb hc

/--
[bsk_augG_adj_inl_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bskspanningtree.lean)
-/
@[path]
private lemma bsk_augG_adj_inl_inl_eq
  {d : ℕ}
  {H : SimpleGraph V}
  {par : Leaf → V}
  {a b : V} :
-- imply
  (bsk_augG H par).Adj (Sum.inl a) (Sum.inl b) ↔ H.Adj a b := by
-- proof
  apply StatMech.Walls.bsk_augG_adj_inl_inl

/--
[bsk_augG_adj_inr_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bskspanningtree.lean)
-/
@[path]
private lemma bsk_augG_adj_inr_inl_eq
  {d : ℕ}
  {H : SimpleGraph V}
  {par : Leaf → V}
  {l : Leaf}
  {a : V} :
-- imply
  (bsk_augG H par).Adj (Sum.inr l) (Sum.inl a) ↔ par l = a := by
-- proof
  apply StatMech.Walls.bsk_augG_adj_inr_inl

/--
[bsk_augG_adj_inl_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bskspanningtree.lean)
-/
@[path]
private lemma bsk_augG_adj_inl_inr_eq
  {d : ℕ}
  {H : SimpleGraph V}
  {par : Leaf → V}
  {l : Leaf}
  {a : V} :
-- imply
  (bsk_augG H par).Adj (Sum.inl a) (Sum.inr l) ↔ par l = a := by
-- proof
  apply StatMech.Walls.bsk_augG_adj_inl_inr

/--
[bsk_augG_not_adj_inr_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bskspanningtree.lean)
-/
@[path]
private lemma bsk_augG_not_adj_inr_inr_eq
  {d : ℕ}
  {H : SimpleGraph V}
  {par : Leaf → V}
  {l l' : Leaf} :
-- imply
  ¬ (bsk_augG H par).Adj (Sum.inr l) (Sum.inr l') := by
-- proof
  apply StatMech.Walls.bsk_augG_not_adj_inr_inr

/--
[bsk_augG_neighborSet_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bskspanningtree.lean)
-/
@[path]
private lemma bsk_augG_neighborSet_inr_eq
  {d : ℕ}
  {H : SimpleGraph V}
  {par : Leaf → V}
  {l : Leaf} :
-- imply
  (bsk_augG H par).neighborSet (Sum.inr l) = {Sum.inl (par l)} := by
-- proof
  apply StatMech.Walls.bsk_augG_neighborSet_inr

/--
[bsk_augG_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bskspanningtree.lean)
-/
@[path]
private lemma bsk_augG_acyclic_eq
  {d : ℕ}
  {H : SimpleGraph V}
  {par : Leaf → V}
-- given
  (hH : H.IsAcyclic) :
-- imply
  (bsk_augG H par).IsAcyclic := by
-- proof
  apply StatMech.Walls.bsk_augG_acyclic H par hH

/--
[bsk_augG_leaf_deg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bskspanningtree.lean)
-/
@[path]
private lemma bsk_augG_leaf_deg_one_eq
  {d : ℕ}
  {V Leaf : Type}
  [Fintype V]
  [DecidableEq V]
  [Fintype Leaf]
  [DecidableEq Leaf]
  {H : SimpleGraph V}
  {par : Leaf → V}
  {l : Leaf} :
-- imply
  (bsk_augG H par).degree (Sum.inr l) = 1 := by
-- proof
  apply StatMech.Walls.bsk_augG_leaf_deg_one H par l

/--
[bsk_exploration_of_augmentedTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bskspanningtree.lean)
-/
@[path]
private lemma bsk_exploration_of_augmentedTree_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {V Leaf : Type}
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  [Fintype Leaf]
  [DecidableEq Leaf]
  {H : SimpleGraph V}
  {par : Leaf → V}
  {trifIdx : Site d → V}
  {compLeaf : Leaf → Set (Site d)}
-- given
  (hH : H.IsAcyclic)
  (hall3 : ∀ a : V, 3 ≤ (bsk_augG H par).degree (Sum.inl a))
  (hinj : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → ∀ z, z ∈ box d R → btr_IsGenuineCoarseTrif ω L z → trifIdx y = trifIdx z → y = z)
  (hcompB : ∀ l : Leaf, (compLeaf l ∩ vertexBoundary d R).Nonempty)
  (hcompD : ∀ l l' : Leaf, l ≠ l' → Disjoint (compLeaf l) (compLeaf l')) :
-- imply
  bfg_GenuineExploration ω L R := by
-- proof
  apply StatMech.Walls.bsk_exploration_of_augmentedTree ω L R H par hH trifIdx compLeaf hall3 hinj hcompB hcompD

/--
[bsk_exploration_of_armTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bskspanningtree.lean)
-/
@[path]
private lemma bsk_exploration_of_armTree_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {V Leaf : Type}
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  [Fintype Leaf]
  [DecidableEq Leaf]
  {H : SimpleGraph V}
  {par : Leaf → V}
  {trifIdx : Site d → V}
  {compLeaf : Leaf → Set (Site d)}
-- given
  (hH : H.IsAcyclic)
  (harm : ∀ a : V, ∃ x y z : V ⊕ Leaf, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ (bsk_augG H par).Adj (Sum.inl a) x ∧ (bsk_augG H par).Adj (Sum.inl a) y ∧ (bsk_augG H par).Adj (Sum.inl a) z)
  (hinj : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → ∀ z, z ∈ box d R → btr_IsGenuineCoarseTrif ω L z → trifIdx y = trifIdx z → y = z)
  (hcompB : ∀ l : Leaf, (compLeaf l ∩ vertexBoundary d R).Nonempty)
  (hcompD : ∀ l l' : Leaf, l ≠ l' → Disjoint (compLeaf l) (compLeaf l')) :
-- imply
  bfg_GenuineExploration ω L R := by
-- proof
  apply StatMech.Walls.bsk_exploration_of_armTree ω L R H par hH trifIdx compLeaf harm hinj hcompB hcompD

/--
[bsk_genuineForest_of_augmentedTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bskspanningtree.lean)
-/
@[path]
private lemma bsk_genuineForest_of_augmentedTree_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {V Leaf : Type}
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  [Fintype Leaf]
  [DecidableEq Leaf]
  {H : SimpleGraph V}
  {par : Leaf → V}
  {trifIdx : Site d → V}
  {compLeaf : Leaf → Set (Site d)}
-- given
  (hH : H.IsAcyclic)
  (hall3 : ∀ a : V, 3 ≤ (bsk_augG H par).degree (Sum.inl a))
  (hinj : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → ∀ z, z ∈ box d R → btr_IsGenuineCoarseTrif ω L z → trifIdx y = trifIdx z → y = z)
  (hcompB : ∀ l : Leaf, (compLeaf l ∩ vertexBoundary d R).Nonempty)
  (hcompD : ∀ l l' : Leaf, l ≠ l' → Disjoint (compLeaf l) (compLeaf l')) :
-- imply
  bgt_GenuineForest ω L R := by
-- proof
  apply StatMech.Walls.bsk_genuineForest_of_augmentedTree ω L R H par hH trifIdx compLeaf hall3 hinj hcompB hcompD

/--
[bsk_genuineTcount_of_augmentedTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bskspanningtree.lean)
-/
@[path]
private lemma bsk_genuineTcount_of_augmentedTree_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {V Leaf : Type}
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  [Fintype Leaf]
  [DecidableEq Leaf]
  {H : SimpleGraph V}
  {par : Leaf → V}
  {trifIdx : Site d → V}
  {compLeaf : Leaf → Set (Site d)}
-- given
  (hH : H.IsAcyclic)
  (hall3 : ∀ a : V, 3 ≤ (bsk_augG H par).degree (Sum.inl a))
  (hinj : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → ∀ z, z ∈ box d R → btr_IsGenuineCoarseTrif ω L z → trifIdx y = trifIdx z → y = z)
  (hcompB : ∀ l : Leaf, (compLeaf l ∩ vertexBoundary d R).Nonempty)
  (hcompD : ∀ l l' : Leaf, l ≠ l' → Disjoint (compLeaf l) (compLeaf l')) :
-- imply
  (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bsk_genuineTcount_of_augmentedTree ω L R H par hH trifIdx compLeaf hall3 hinj hcompB hcompD

/--
[bsk_exploration_of_connectedForestData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bskspanningtree.lean)
-/
@[path]
private lemma bsk_exploration_of_connectedForestData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bsk_ConnectedForestData ω L R) :
-- imply
  bfg_GenuineExploration ω L R := by
-- proof
  apply StatMech.Walls.bsk_exploration_of_connectedForestData ω L R h

/--
[bsk_bk_count_of_connectedForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bskspanningtree.lean)
-/
@[path]
private lemma bsk_bk_count_of_connectedForest_eq
  {d : ℕ}
  {L R : ℕ}
-- given
  (hdata : ∀ ω : ConfigSpace (Sym2 (Site d)), bsk_ConnectedForestData ω L R) :
-- imply
  ∀ ω : ConfigSpace (Sym2 (Site d)), (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bsk_bk_count_of_connectedForest L R hdata

/--
[bsk_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bskspanningtree.lean)
-/
@[path]
private lemma bsk_status_eq
  {d : ℕ} :
-- imply
  (∀ {V Leaf : Type*} (H : SimpleGraph V) (par : Leaf → V), H.IsAcyclic → (bsk_augG H par).IsAcyclic) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bsk_ConnectedForestData ω L R → bfg_GenuineExploration ω L R) ∧ (∀ {V : Type} (G : SimpleGraph V), G.Connected → ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree) ∧ (∀ (L R : ℕ), (∀ ω : ConfigSpace (Sym2 (Site d)), bsk_ConnectedForestData ω L R) → ∀ ω : ConfigSpace (Sym2 (Site d)), (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R) := by
-- proof
  apply StatMech.Walls.bsk_status


-- created on 2026-10-23
