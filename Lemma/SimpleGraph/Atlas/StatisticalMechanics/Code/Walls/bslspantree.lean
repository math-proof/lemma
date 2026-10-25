import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bslspantree
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bsl_count_via_connectedForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bslspantree.lean)
-/
@[path]
private lemma bsl_count_via_connectedForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc69_Gn_globalForest ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bsl_count_via_connectedForest ω L R h

/--
[bsl_unconditional_leaf_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bslspantree.lean)
-/
@[path]
private lemma bsl_unconditional_leaf_bound_eq
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
  apply StatMech.Walls.bsl_unconditional_leaf_bound G hacyc hmin

/--
[bsl_globalForest_of_connected_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bslspantree.lean)
-/
@[path]
private lemma bsl_globalForest_of_connected_carrier_eq
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
  apply StatMech.Walls.bsl_globalForest_of_connected_carrier ω L R G hGac ιU harm hinj hFmin

/--
[bsl_spanForest_is_valid_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bslspantree.lean)
-/
@[path]
private lemma bsl_spanForest_is_valid_carrier_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {S : Set (Site d)}
  [hSfin : Fintype (↑S : Type)]
  [hSne : Nonempty (↑S : Type)]
  {G₀ : SimpleGraph (↑S : Type)}
  [DecidableRel (osf_spanForest G₀).Adj]
  {ιU : Site d → (↑S : Type)}
-- given
  (harm : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∃ t₁ t₂ t₃ : (↑S : Type), bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧ ιU y ≠ t₁ ∧ ιU y ≠ t₂ ∧ ιU y ≠ t₃ ∧ (osf_spanForest G₀).Reachable (ιU y) t₁ ∧ (osf_spanForest G₀).Reachable (ιU y) t₂ ∧ (osf_spanForest G₀).Reachable (ιU y) t₃ ∧ ¬ ((osf_spanForest G₀).deleteIncidenceSet (ιU y)).Reachable t₁ t₂ ∧ ¬ ((osf_spanForest G₀).deleteIncidenceSet (ιU y)).Reachable t₁ t₃ ∧ ¬ ((osf_spanForest G₀).deleteIncidenceSet (ιU y)).Reachable t₂ t₃)
  (hinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R → bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z)
  (hFmin : ∀ (F : SimpleGraph (↑S : Type)) [DecidableRel F.Adj], F ≤ osf_spanForest G₀ → F.IsAcyclic → (∀ v : (↑S : Type), F.degree v = 1 → bc121_Protected ω L R ιU v) → (∀ a b : (↑S : Type), bc121_Protected ω L R ιU a → bc121_Protected ω L R ιU b → (osf_spanForest G₀).Reachable a b → F.Reachable a b) → ∀ v : (↑S : Type), 1 ≤ F.degree v) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bsl_spanForest_is_valid_carrier ω L R G₀ ιU harm hinj hFmin

/--
[bsl_connected_needs_no_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bslspantree.lean)
-/
@[path]
private lemma bsl_connected_needs_no_injection_eq
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
  bc69_Gn_globalForest ω L R ∧ bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bsl_connected_needs_no_injection ω L R G hGac ιU harm hinj hFmin

/--
[bsl_withinHub_targets_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bslspantree.lean)
-/
@[path]
private lemma bsl_withinHub_targets_free_eq
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
  ∃ z₁ z₂ z₃ : Site d, (z₁ ∈ vertexBoundary d R ∧ z₂ ∈ vertexBoundary d R ∧ z₃ ∈ vertexBoundary d R) ∧ (¬ (bc67_contractedLattice ω L y).Reachable z₁ z₂ ∧ ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₃ ∧ ¬ (bc67_contractedLattice ω L y).Reachable z₂ z₃) ∧ (z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃) := by
-- proof
  apply StatMech.Walls.bsl_withinHub_targets_free ω L R hR y a₁ a₂ a₃ hb₁ hb₂ hb₃ hi₁ hi₂ hi₃ hc₁₂ hc₁₃ hc₂₃

/--
[bsl_perNode_cut_still_cross_hub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bslspantree.lean)
-/
@[path]
private lemma bsl_perNode_cut_still_cross_hub_eq
  {d : ℕ} :
-- imply
  ((SimpleGraph.fromEdgeSet {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet (0 : Fin 5)).Reachable 2 4 := by
-- proof
  apply StatMech.Walls.bsl_perNode_cut_still_cross_hub

/--
[bsl_obstruction_carrier_is_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bslspantree.lean)
-/
@[path]
private lemma bsl_obstruction_carrier_is_connected_eq
  {d : ℕ} :
-- imply
  (SimpleGraph.fromEdgeSet {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).Reachable 1 4 := by
-- proof
  apply StatMech.Walls.bsl_obstruction_carrier_is_connected

/--
[bsl_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bslspantree.lean)
-/
@[path]
private lemma bsl_nonvacuous_eq
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
  apply StatMech.Walls.bsl_nonvacuous ω L R hz₀ hz₁ hzne hno

/--
[bsl_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bslspantree.lean)
-/
@[path]
private lemma bsl_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) ∧ (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (osf_spanForest G).IsAcyclic) ∧ (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj], G.IsAcyclic → (∀ v, 1 ≤ G.degree v) → (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card) ∧ (((SimpleGraph.fromEdgeSet {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet (0 : Fin 5)).Reachable 2 4) := by
-- proof
  apply StatMech.Walls.bsl_status


-- created on 2026-10-23
