import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bctconnectedtree.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bct_fiberForest_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bctconnectedtree.lean)
-/
@[path]
private lemma bct_fiberForest_adj_iff_eq
  {d : ℕ}
  {β V : Type}
  {H : SimpleGraph V}
  {p q : β × V} :
-- imply
  (bct_fiberForest β V H).Adj p q ↔ (p.1 = q.1 ∧ H.Adj p.2 q.2) := by
-- proof
  apply StatMech.Walls.bct_fiberForest_adj_iff

/--
[bct_fiberForest_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bctconnectedtree.lean)
-/
@[path]
private lemma bct_fiberForest_fst_eq
  {d : ℕ}
  {β V : Type}
  {H : SimpleGraph V}
  {p q : β × V}
-- given
  (h : (bct_fiberForest β V H).Adj p q) :
-- imply
  p.1 = q.1 := by
-- proof
  apply StatMech.Walls.bct_fiberForest_fst h

/--
[bct_walk_fst_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bctconnectedtree.lean)
-/
@[path]
private lemma bct_walk_fst_const_eq
  {d : ℕ}
  {β V : Type}
  {H : SimpleGraph V}
  {p q : β × V}
  {w : (bct_fiberForest β V H).Walk p q} :
-- imply
  ∀ v ∈ w.support, v.1 = p.1 := by
-- proof
  apply StatMech.Walls.bct_walk_fst_const w

/--
[bct_snd_injOn_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bctconnectedtree.lean)
-/
@[path]
private lemma bct_snd_injOn_support_eq
  {d : ℕ}
  {β V : Type}
  {H : SimpleGraph V}
  {v : β × V}
  {c : (bct_fiberForest β V H).Walk v v} :
-- imply
  Set.InjOn (Prod.snd : β × V → V) {x | x ∈ c.support} := by
-- proof
  apply StatMech.Walls.bct_snd_injOn_support c

/--
[bct_fiberForest_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bctconnectedtree.lean)
-/
@[path]
private lemma bct_fiberForest_acyclic_eq
  {d : ℕ}
  {β V : Type}
  {H : SimpleGraph V}
-- given
  (hH : H.IsAcyclic) :
-- imply
  (bct_fiberForest β V H).IsAcyclic := by
-- proof
  apply StatMech.Walls.bct_fiberForest_acyclic β V H hH

/--
[bct_fiberForest_neighborFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bctconnectedtree.lean)
-/
@[path]
private lemma bct_fiberForest_neighborFinset_eq
  {d : ℕ}
  {β V : Type}
  [DecidableEq β]
  [Fintype β]
  [DecidableEq V]
  [Fintype V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {t : β}
  {i : V} :
-- imply
  (bct_fiberForest β V H).neighborFinset (t, i) = ({t} : Finset β) ×ˢ (H.neighborFinset i) := by
-- proof
  apply StatMech.Walls.bct_fiberForest_neighborFinset H t i

/--
[bct_fiberForest_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bctconnectedtree.lean)
-/
@[path]
private lemma bct_fiberForest_degree_eq
  {d : ℕ}
  {β V : Type}
  [DecidableEq β]
  [Fintype β]
  [DecidableEq V]
  [Fintype V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {t : β}
  {i : V} :
-- imply
  (bct_fiberForest β V H).degree (t, i) = H.degree i := by
-- proof
  apply StatMech.Walls.bct_fiberForest_degree H t i

/--
[bct_dstarG_isTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bctconnectedtree.lean)
-/
@[path]
private lemma bct_dstarG_isTree_eq
  {d : ℕ} :
-- imply
  bct_dstarG.IsTree := by
-- proof
  apply StatMech.Walls.bct_dstarG_isTree

/--
[bct_dstarG_isAcyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bctconnectedtree.lean)
-/
@[path]
private lemma bct_dstarG_isAcyclic_eq
  {d : ℕ} :
-- imply
  bct_dstarG.IsAcyclic := by
-- proof
  apply StatMech.Walls.bct_dstarG_isAcyclic

/--
[bct_dstarG_hub0_deg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bctconnectedtree.lean)
-/
@[path]
private lemma bct_dstarG_hub0_deg_eq
  {d : ℕ} :
-- imply
  bct_dstarG.degree 0 = 3 := by
-- proof
  apply StatMech.Walls.bct_dstarG_hub0_deg

/--
[bct_dstarG_hub1_deg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bctconnectedtree.lean)
-/
@[path]
private lemma bct_dstarG_hub1_deg_eq
  {d : ℕ} :
-- imply
  bct_dstarG.degree 1 = 3 := by
-- proof
  apply StatMech.Walls.bct_dstarG_hub1_deg

/--
[bct_dstarG_leaf_deg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bctconnectedtree.lean)
-/
@[path]
private lemma bct_dstarG_leaf_deg_eq
  {d : ℕ} :
-- imply
  ∀ i : Fin 6, i ≠ 0 → i ≠ 1 → bct_dstarG.degree i = 1 := by
-- proof
  apply StatMech.Walls.bct_dstarG_leaf_deg

/--
[bct_dstarG_min_deg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bctconnectedtree.lean)
-/
@[path]
private lemma bct_dstarG_min_deg_eq
  {d : ℕ} :
-- imply
  ∀ i : Fin 6, 1 ≤ bct_dstarG.degree i := by
-- proof
  apply StatMech.Walls.bct_dstarG_min_deg

/--
[bct_dstarG_deg1_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bctconnectedtree.lean)
-/
@[path]
private lemma bct_dstarG_deg1_iff_eq
  {d : ℕ}
  {i : Fin 6} :
-- imply
  bct_dstarG.degree i = 1 ↔ (i ≠ 0 ∧ i ≠ 1) := by
-- proof
  apply StatMech.Walls.bct_dstarG_deg1_iff i

/--
[bct_exploration_of_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bctconnectedtree.lean)
-/
@[path]
private lemma bct_exploration_of_carrier_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {W : Type}
  [Fintype W]
  [Nonempty W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {ιT : Site d → W}
  {comp : W → Set (Site d)}
-- given
  (hacyc : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v)
  (hdeg3 : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → 3 ≤ G.degree (ιT y))
  (hinj : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → ∀ z, z ∈ box d R → btr_IsGenuineCoarseTrif ω L z → ιT y = ιT z → y = z)
  (hbnd : ∀ v, G.degree v = 1 → (comp v ∩ vertexBoundary d R).Nonempty)
  (hdisj : ∀ u, G.degree u = 1 → ∀ v, G.degree v = 1 → u ≠ v → Disjoint (comp u) (comp v)) :
-- imply
  bfg_GenuineExploration ω L R := by
-- proof
  apply StatMech.Walls.bct_exploration_of_carrier ω L R W G ιT comp hacyc hmin hdeg3 hinj hbnd hdisj

/--
[bct_exploration_of_twoSharedTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bctconnectedtree.lean)
-/
@[path]
private lemma bct_exploration_of_twoSharedTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y₀ y₁ : Site d}
  {comp : Fin 6 → Set (Site d)}
-- given
  (hy0 : btr_IsGenuineCoarseTrif ω L y₀)
  (hy1 : btr_IsGenuineCoarseTrif ω L y₁)
  (hy0box : y₀ ∈ box d R)
  (hy1box : y₁ ∈ box d R)
  (hne : y₀ ≠ y₁)
  (huniq : ∀ z, z ∈ box d R → btr_IsGenuineCoarseTrif ω L z → z = y₀ ∨ z = y₁)
  (hcompB : ∀ i : Fin 6, i ≠ 0 → i ≠ 1 → (comp i ∩ vertexBoundary d R).Nonempty)
  (hcompD : ∀ i : Fin 6, i ≠ 0 → i ≠ 1 → ∀ j : Fin 6, j ≠ 0 → j ≠ 1 → i ≠ j → Disjoint (comp i) (comp j)) :
-- imply
  bfg_GenuineExploration ω L R := by
-- proof
  apply StatMech.Walls.bct_exploration_of_twoSharedTrif ω L R hy0 hy1 hy0box hy1box hne huniq comp hcompB hcompD

/--
[bct_genuineForest_of_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bctconnectedtree.lean)
-/
@[path]
private lemma bct_genuineForest_of_carrier_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {W : Type}
  [Fintype W]
  [Nonempty W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {ιT : Site d → W}
  {comp : W → Set (Site d)}
-- given
  (hacyc : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v)
  (hdeg3 : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → 3 ≤ G.degree (ιT y))
  (hinj : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → ∀ z, z ∈ box d R → btr_IsGenuineCoarseTrif ω L z → ιT y = ιT z → y = z)
  (hbnd : ∀ v, G.degree v = 1 → (comp v ∩ vertexBoundary d R).Nonempty)
  (hdisj : ∀ u, G.degree u = 1 → ∀ v, G.degree v = 1 → u ≠ v → Disjoint (comp u) (comp v)) :
-- imply
  bgt_GenuineForest ω L R := by
-- proof
  apply StatMech.Walls.bct_genuineForest_of_carrier ω L R W G ιT comp hacyc hmin hdeg3 hinj hbnd hdisj

/--
[bct_genuineTcount_of_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bctconnectedtree.lean)
-/
@[path]
private lemma bct_genuineTcount_of_carrier_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {W : Type}
  [Fintype W]
  [Nonempty W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {ιT : Site d → W}
  {comp : W → Set (Site d)}
-- given
  (hacyc : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v)
  (hdeg3 : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → 3 ≤ G.degree (ιT y))
  (hinj : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → ∀ z, z ∈ box d R → btr_IsGenuineCoarseTrif ω L z → ιT y = ιT z → y = z)
  (hbnd : ∀ v, G.degree v = 1 → (comp v ∩ vertexBoundary d R).Nonempty)
  (hdisj : ∀ u, G.degree u = 1 → ∀ v, G.degree v = 1 → u ≠ v → Disjoint (comp u) (comp v)) :
-- imply
  (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bct_genuineTcount_of_carrier ω L R W G ιT comp hacyc hmin hdeg3 hinj hbnd hdisj

/--
[bct_twoSharedTrif_genuineForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bctconnectedtree.lean)
-/
@[path]
private lemma bct_twoSharedTrif_genuineForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y₀ y₁ : Site d}
  {comp : Fin 6 → Set (Site d)}
-- given
  (hy0 : btr_IsGenuineCoarseTrif ω L y₀)
  (hy1 : btr_IsGenuineCoarseTrif ω L y₁)
  (hy0box : y₀ ∈ box d R)
  (hy1box : y₁ ∈ box d R)
  (hne : y₀ ≠ y₁)
  (huniq : ∀ z, z ∈ box d R → btr_IsGenuineCoarseTrif ω L z → z = y₀ ∨ z = y₁)
  (hcompB : ∀ i : Fin 6, i ≠ 0 → i ≠ 1 → (comp i ∩ vertexBoundary d R).Nonempty)
  (hcompD : ∀ i : Fin 6, i ≠ 0 → i ≠ 1 → ∀ j : Fin 6, j ≠ 0 → j ≠ 1 → i ≠ j → Disjoint (comp i) (comp j)) :
-- imply
  bgt_GenuineForest ω L R := by
-- proof
  apply StatMech.Walls.bct_twoSharedTrif_genuineForest ω L R hy0 hy1 hy0box hy1box hne huniq comp hcompB hcompD

/--
[bct_genuineTcount_of_connectedTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bctconnectedtree.lean)
-/
@[path]
private lemma bct_genuineTcount_of_connectedTree_eq
  {d : ℕ}
  {L R : ℕ}
-- given
  (hexpl : ∀ ω : ConfigSpace (Sym2 (Site d)), bfg_GenuineExploration ω L R) :
-- imply
  ∀ ω : ConfigSpace (Sym2 (Site d)), (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bct_genuineTcount_of_connectedTree L R hexpl

/--
[bct_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bctconnectedtree.lean)
-/
@[path]
private lemma bct_status_eq
  {d : ℕ} :
-- imply
  (∀ (β V : Type) (H : SimpleGraph V), H.IsAcyclic → (bct_fiberForest β V H).IsAcyclic) ∧ bct_dstarG.IsTree ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (W : Type) [Fintype W] [Nonempty W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj] (ιT : Site d → W) (comp : W → Set (Site d)), G.IsAcyclic → (∀ v, 1 ≤ G.degree v) → (∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → 3 ≤ G.degree (ιT y)) → (∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → ∀ z, z ∈ box d R → btr_IsGenuineCoarseTrif ω L z → ιT y = ιT z → y = z) → (∀ v, G.degree v = 1 → (comp v ∩ vertexBoundary d R).Nonempty) → (∀ u, G.degree u = 1 → ∀ v, G.degree v = 1 → u ≠ v → Disjoint (comp u) (comp v)) → bfg_GenuineExploration ω L R) ∧ (∀ (L R : ℕ), (∀ ω : ConfigSpace (Sym2 (Site d)), bfg_GenuineExploration ω L R) → ∀ ω : ConfigSpace (Sym2 (Site d)), (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R) := by
-- proof
  apply StatMech.Walls.bct_status


-- created on 2026-10-23
