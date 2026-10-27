import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bkfforest.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bkf_connectedForest_closes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkfforest.lean)
-/
@[path]
private lemma bkf_connectedForest_closes_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {S : Set (Site d)}
  [hSfin : Fintype (↑S : Type)]
  [hSne : Nonempty (↑S : Type)]
  {G : SimpleGraph (↑S : Type)}
  [DecidableRel G.Adj]
  {ιU : Site d → (↑S : Type)}
-- given
  (hGac : G.IsAcyclic)
  (harm : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∃ t₁ t₂ t₃ : (↑S : Type), bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧ ιU y ≠ t₁ ∧ ιU y ≠ t₂ ∧ ιU y ≠ t₃ ∧ G.Reachable (ιU y) t₁ ∧ G.Reachable (ιU y) t₂ ∧ G.Reachable (ιU y) t₃ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₂ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₃ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₂ t₃)
  (hinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R → bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z)
  (hFmin : ∀ (F : SimpleGraph (↑S : Type)) [DecidableRel F.Adj], F ≤ G → F.IsAcyclic → (∀ v : (↑S : Type), F.degree v = 1 → bc121_Protected ω L R ιU v) → (∀ a b : (↑S : Type), bc121_Protected ω L R ιU a → bc121_Protected ω L R ιU b → G.Reachable a b → F.Reachable a b) → ∀ v : (↑S : Type), 1 ≤ F.degree v) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bkf_connectedForest_closes ω L R G hGac ιU harm hinj hFmin

/--
[bkf_count_via_connectedForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkfforest.lean)
-/
@[path]
private lemma bkf_count_via_connectedForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {S : Set (Site d)}
  [hSfin : Fintype (↑S : Type)]
  [hSne : Nonempty (↑S : Type)]
  {G : SimpleGraph (↑S : Type)}
  [DecidableRel G.Adj]
  {ιU : Site d → (↑S : Type)}
-- given
  (hGac : G.IsAcyclic)
  (harm : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∃ t₁ t₂ t₃ : (↑S : Type), bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧ ιU y ≠ t₁ ∧ ιU y ≠ t₂ ∧ ιU y ≠ t₃ ∧ G.Reachable (ιU y) t₁ ∧ G.Reachable (ιU y) t₂ ∧ G.Reachable (ιU y) t₃ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₂ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₃ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₂ t₃)
  (hinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R → bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z)
  (hFmin : ∀ (F : SimpleGraph (↑S : Type)) [DecidableRel F.Adj], F ≤ G → F.IsAcyclic → (∀ v : (↑S : Type), F.degree v = 1 → bc121_Protected ω L R ιU v) → (∀ a b : (↑S : Type), bc121_Protected ω L R ιU a → bc121_Protected ω L R ιU b → G.Reachable a b → F.Reachable a b) → ∀ v : (↑S : Type), 1 ≤ F.degree v) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bkf_count_via_connectedForest ω L R G hGac ιU harm hinj hFmin

/--
[bkf_sharedLeaf_cut_survives](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkfforest.lean)
-/
@[path]
private lemma bkf_sharedLeaf_cut_survives_eq
  {d : ℕ} :
-- imply
  ¬ ((SimpleGraph.fromEdgeSet {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet (0 : Fin 5)).Reachable 1 2 := by
-- proof
  apply StatMech.Walls.bkf_sharedLeaf_cut_survives

/--
[bkf_disjointStar_obstruction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkfforest.lean)
-/
@[path]
private lemma bkf_disjointStar_obstruction_eq
  {d : ℕ} :
-- imply
  ((SimpleGraph.fromEdgeSet {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet (0 : Fin 5)).Reachable 2 4 := by
-- proof
  apply StatMech.Walls.bkf_disjointStar_obstruction

/--
[bkf_sharedLeaf_absorbed_in_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkfforest.lean)
-/
@[path]
private lemma bkf_sharedLeaf_absorbed_in_count_eq
  {d : ℕ}
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hacyc : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v) :
-- imply
  (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card := by
-- proof
  apply StatMech.Walls.bkf_sharedLeaf_absorbed_in_count G hacyc hmin

/--
[bkf_deg3_from_genuine_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkfforest.lean)
-/
@[path]
private lemma bkf_deg3_from_genuine_cut_eq
  {d : ℕ}
  [Fintype V]
  {F : SimpleGraph V}
  [DecidableRel F.Adj]
  {u t₁ t₂ t₃ : V}
-- given
  (hne₁ : u ≠ t₁)
  (hne₂ : u ≠ t₂)
  (hne₃ : u ≠ t₃)
  (hr₁ : F.Reachable u t₁)
  (hr₂ : F.Reachable u t₂)
  (hr₃ : F.Reachable u t₃)
  (hcut₁₂ : ¬ (F.deleteIncidenceSet u).Reachable t₁ t₂)
  (hcut₁₃ : ¬ (F.deleteIncidenceSet u).Reachable t₁ t₃)
  (hcut₂₃ : ¬ (F.deleteIncidenceSet u).Reachable t₂ t₃) :
-- imply
  3 ≤ F.degree u := by
-- proof
  apply StatMech.Walls.bkf_deg3_from_genuine_cut F hne₁ hne₂ hne₃ hr₁ hr₂ hr₃ hcut₁₂ hcut₁₃ hcut₂₃

/--
[bkf_arm_reaches_boundary_targets](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkfforest.lean)
-/
@[path]
private lemma bkf_arm_reaches_boundary_targets_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y a₁ a₂ a₃ : Site d}
-- given
  (hR : 1 ≤ R)
  (hb₁ : a₁ ∈ box d R)
  (hb₂ : a₂ ∈ box d R)
  (hb₃ : a₃ ∈ box d R)
  (hi₁ : (cluster d (removeSites (bc61_boxAround d L y) ω) a₁).Infinite)
  (hi₂ : (cluster d (removeSites (bc61_boxAround d L y) ω) a₂).Infinite)
  (hi₃ : (cluster d (removeSites (bc61_boxAround d L y) ω) a₃).Infinite)
  (hc₁₂ : ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂)
  (hc₁₃ : ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃)
  (hc₂₃ : ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) :
-- imply
  ∃ z₁ z₂ z₃ : Site d, (z₁ ∈ vertexBoundary d R ∧ z₂ ∈ vertexBoundary d R ∧ z₃ ∈ vertexBoundary d R) ∧ ((bc67_contractedLattice ω L y).Reachable a₁ z₁ ∧ (bc67_contractedLattice ω L y).Reachable a₂ z₂ ∧ (bc67_contractedLattice ω L y).Reachable a₃ z₃) ∧ (z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃) := by
-- proof
  apply StatMech.Walls.bkf_arm_reaches_boundary_targets ω L R hR y a₁ a₂ a₃ hb₁ hb₂ hb₃ hi₁ hi₂ hi₃ hc₁₂ hc₁₃ hc₂₃

/--
[bkf_harm_of_cutTransfer_and_targets](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkfforest.lean)
-/
@[path]
private lemma bkf_harm_of_cutTransfer_and_targets_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {S : Set (Site d)}
  {G : SimpleGraph (↑S : Type)}
  {ιU : Site d → (↑S : Type)}
-- given
  (htrans : bkf_CutTransfer ω L R G ιU)
  (htargets : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∃ t₁ t₂ t₃ : (↑S : Type), bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧ ιU y ≠ t₁ ∧ ιU y ≠ t₂ ∧ ιU y ≠ t₃ ∧ G.Reachable (ιU y) t₁ ∧ G.Reachable (ιU y) t₂ ∧ G.Reachable (ιU y) t₃ ∧ ¬ (bc67_contractedLattice ω L y).Reachable (t₁ : Site d) (t₂ : Site d) ∧ ¬ (bc67_contractedLattice ω L y).Reachable (t₁ : Site d) (t₃ : Site d) ∧ ¬ (bc67_contractedLattice ω L y).Reachable (t₂ : Site d) (t₃ : Site d)) :
-- imply
  ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∃ t₁ t₂ t₃ : (↑S : Type), bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧ ιU y ≠ t₁ ∧ ιU y ≠ t₂ ∧ ιU y ≠ t₃ ∧ G.Reachable (ιU y) t₁ ∧ G.Reachable (ιU y) t₂ ∧ G.Reachable (ιU y) t₃ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₂ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₃ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₂ t₃ := by
-- proof
  apply StatMech.Walls.bkf_harm_of_cutTransfer_and_targets ω L R G ιU htrans htargets

/--
[bkf_connectedForest_closes_of_cutTransfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkfforest.lean)
-/
@[path]
private lemma bkf_connectedForest_closes_of_cutTransfer_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {S : Set (Site d)}
  [hSfin : Fintype (↑S : Type)]
  [hSne : Nonempty (↑S : Type)]
  {G : SimpleGraph (↑S : Type)}
  [DecidableRel G.Adj]
  {ιU : Site d → (↑S : Type)}
-- given
  (hGac : G.IsAcyclic)
  (htrans : bkf_CutTransfer ω L R G ιU)
  (htargets : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∃ t₁ t₂ t₃ : (↑S : Type), bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧ ιU y ≠ t₁ ∧ ιU y ≠ t₂ ∧ ιU y ≠ t₃ ∧ G.Reachable (ιU y) t₁ ∧ G.Reachable (ιU y) t₂ ∧ G.Reachable (ιU y) t₃ ∧ ¬ (bc67_contractedLattice ω L y).Reachable (t₁ : Site d) (t₂ : Site d) ∧ ¬ (bc67_contractedLattice ω L y).Reachable (t₁ : Site d) (t₃ : Site d) ∧ ¬ (bc67_contractedLattice ω L y).Reachable (t₂ : Site d) (t₃ : Site d))
  (hinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R → bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z)
  (hFmin : ∀ (F : SimpleGraph (↑S : Type)) [DecidableRel F.Adj], F ≤ G → F.IsAcyclic → (∀ v : (↑S : Type), F.degree v = 1 → bc121_Protected ω L R ιU v) → (∀ a b : (↑S : Type), bc121_Protected ω L R ιU a → bc121_Protected ω L R ιU b → G.Reachable a b → F.Reachable a b) → ∀ v : (↑S : Type), 1 ≤ F.degree v) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bkf_connectedForest_closes_of_cutTransfer ω L R G hGac ιU htrans htargets hinj hFmin

/--
[bkf_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkfforest.lean)
-/
@[path]
private lemma bkf_nonvacuous_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁)
  (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bkf_nonvacuous ω L R hz₀ hz₁ hzne hno

/--
[bkf_cutTransfer_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkfforest.lean)
-/
@[path]
private lemma bkf_cutTransfer_nonvacuous_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {S : Set (Site d)}
  {G : SimpleGraph (↑S : Type)}
  {ιU : Site d → (↑S : Type)}
-- given
  (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
-- imply
  bkf_CutTransfer ω L R G ιU := by
-- proof
  apply StatMech.Walls.bkf_cutTransfer_nonvacuous ω L R G ιU hno

/--
[bkf_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkfforest.lean)
-/
@[path]
private lemma bkf_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) {S : Set (Site d)} [Fintype (↑S : Type)] [Nonempty (↑S : Type)] (G : SimpleGraph (↑S : Type)) [DecidableRel G.Adj], G.IsAcyclic → ∀ (ιU : Site d → (↑S : Type)), (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∃ t₁ t₂ t₃ : (↑S : Type), bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧ ιU y ≠ t₁ ∧ ιU y ≠ t₂ ∧ ιU y ≠ t₃ ∧ G.Reachable (ιU y) t₁ ∧ G.Reachable (ιU y) t₂ ∧ G.Reachable (ιU y) t₃ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₂ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₃ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₂ t₃) → (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R → bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z) → (∀ (F : SimpleGraph (↑S : Type)) [DecidableRel F.Adj], F ≤ G → F.IsAcyclic → (∀ v : (↑S : Type), F.degree v = 1 → bc121_Protected ω L R ιU v) → (∀ a b : (↑S : Type), bc121_Protected ω L R ιU a → bc121_Protected ω L R ιU b → G.Reachable a b → F.Reachable a b) → ∀ v : (↑S : Type), 1 ≤ F.degree v) → bc69_Gn_globalForest ω L R) ∧ (¬ ((SimpleGraph.fromEdgeSet {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet (0 : Fin 5)).Reachable 1 2) ∧ (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj], G.IsAcyclic → (∀ v, 1 ≤ G.degree v) → (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) {S : Set (Site d)} [Fintype (↑S : Type)] [Nonempty (↑S : Type)] (G : SimpleGraph (↑S : Type)) [DecidableRel G.Adj], G.IsAcyclic → ∀ (ιU : Site d → (↑S : Type)), bkf_CutTransfer ω L R G ιU → (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∃ t₁ t₂ t₃ : (↑S : Type), bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧ ιU y ≠ t₁ ∧ ιU y ≠ t₂ ∧ ιU y ≠ t₃ ∧ G.Reachable (ιU y) t₁ ∧ G.Reachable (ιU y) t₂ ∧ G.Reachable (ιU y) t₃ ∧ ¬ (bc67_contractedLattice ω L y).Reachable (t₁ : Site d) (t₂ : Site d) ∧ ¬ (bc67_contractedLattice ω L y).Reachable (t₁ : Site d) (t₃ : Site d) ∧ ¬ (bc67_contractedLattice ω L y).Reachable (t₂ : Site d) (t₃ : Site d)) → (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R → bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z) → (∀ (F : SimpleGraph (↑S : Type)) [DecidableRel F.Adj], F ≤ G → F.IsAcyclic → (∀ v : (↑S : Type), F.degree v = 1 → bc121_Protected ω L R ιU v) → (∀ a b : (↑S : Type), bc121_Protected ω L R ιU a → bc121_Protected ω L R ιU b → G.Reachable a b → F.Reachable a b) → ∀ v : (↑S : Type), 1 ≤ F.degree v) → bc69_Gn_globalForest ω L R) := by
-- proof
  apply StatMech.Walls.bkf_status


-- created on 2026-10-23
