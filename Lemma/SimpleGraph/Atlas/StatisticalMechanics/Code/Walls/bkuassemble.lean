import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bkuassemble
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bku_armPathCarrier_closes_bc69](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkuassemble.lean)
-/
@[path]
private lemma bku_armPathCarrier_closes_bc69_eq
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
  (harm : bku_armPathCarrier ω L R G ιU)
  (hinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R → bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z)
  (hFmin : ∀ (F : SimpleGraph (↑S : Type)) [DecidableRel F.Adj], F ≤ G → F.IsAcyclic → (∀ v : (↑S : Type), F.degree v = 1 → bc121_Protected ω L R ιU v) → (∀ a b : (↑S : Type), bc121_Protected ω L R ιU a → bc121_Protected ω L R ιU b → G.Reachable a b → F.Reachable a b) → ∀ v : (↑S : Type), 1 ≤ F.degree v) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bku_armPathCarrier_closes_bc69 ω L R G hGac ιU harm hinj hFmin

/--
[bku_armPathCarrier_of_cutTransfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkuassemble.lean)
-/
@[path]
private lemma bku_armPathCarrier_of_cutTransfer_eq
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
  bku_armPathCarrier ω L R G ιU := by
-- proof
  apply StatMech.Walls.bku_armPathCarrier_of_cutTransfer ω L R G ιU htrans htargets

/--
[bku_bc69_of_cutTransfer_and_targets](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkuassemble.lean)
-/
@[path]
private lemma bku_bc69_of_cutTransfer_and_targets_eq
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
  apply StatMech.Walls.bku_bc69_of_cutTransfer_and_targets ω L R G hGac ιU htrans htargets hinj hFmin

/--
[bku_within_hub_boundary_targets](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkuassemble.lean)
-/
@[path]
private lemma bku_within_hub_boundary_targets_eq
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
  apply StatMech.Walls.bku_within_hub_boundary_targets ω L R hR y a₁ a₂ a₃ hb₁ hb₂ hb₃ hi₁ hi₂ hi₃ hc₁₂ hc₁₃ hc₂₃

/--
[bku_perHub_cutTransfer_holds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkuassemble.lean)
-/
@[path]
private lemma bku_perHub_cutTransfer_holds_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y a b : Site d}
-- given
  (hcut : ¬ (bc67_contractedLattice ω L y).Reachable a b) :
-- imply
  ¬ ((bkt_ctrGraph ω L y).deleteIncidenceSet none).Reachable (some a) (some b) := by
-- proof
  apply StatMech.Walls.bku_perHub_cutTransfer_holds ω L y a b hcut

/--
[bku_bk_closes_of_armPathCarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkuassemble.lean)
-/
@[path]
private lemma bku_bk_closes_of_armPathCarrier_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hGlobal : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R)
  (hcoarseRoute : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bku_bk_closes_of_armPathCarrier hd p hp1 hp0 L hGlobal hcoarseRoute

/--
[bku_overconnection_relocated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkuassemble.lean)
-/
@[path]
private lemma bku_overconnection_relocated_eq
  {d : ℕ} :
-- imply
  ((SimpleGraph.fromEdgeSet {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet (0 : Fin 5)).Reachable 2 4 := by
-- proof
  apply StatMech.Walls.bku_overconnection_relocated

/--
[bku_box_overconnects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkuassemble.lean)
-/
@[path]
private lemma bku_box_overconnects_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y a b : Site d}
-- given
  (ha : a ∉ bc61_boxAround d L y)
  (hb : b ∉ bc61_boxAround d L y)
  (hia : bc67_GnIncident ω L y a)
  (hib : bc67_GnIncident ω L y b) :
-- imply
  (bkt_ctrGraph ω L y).Reachable (some a) (some b) := by
-- proof
  apply StatMech.Walls.bku_box_overconnects ω L y a b ha hb hia hib

/--
[bku_horn_A_leaf_in_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkuassemble.lean)
-/
@[path]
private lemma bku_horn_A_leaf_in_box_eq
  {d : ℕ}
  {L : ℕ}
  {y : Site d}
  {k : ℤ}
-- given
  (hd : 1 ≤ d)
  (hL : 3 ≤ L)
  (hk : k ∈ bc112_shifts) :
-- imply
  bc112_leaf hd y k ∈ bc61_boxAround d L y := by
-- proof
  apply StatMech.Walls.bku_horn_A_leaf_in_box hd hL y hk

/--
[bku_armPathCarrier_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkuassemble.lean)
-/
@[path]
private lemma bku_armPathCarrier_nonvacuous_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {S : Set (Site d)}
  {G : SimpleGraph (↑S : Type)}
  {ιU : Site d → (↑S : Type)}
-- given
  (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
-- imply
  bku_armPathCarrier ω L R G ιU := by
-- proof
  apply StatMech.Walls.bku_armPathCarrier_nonvacuous ω L R G ιU hno

/--
[bku_route_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkuassemble.lean)
-/
@[path]
private lemma bku_route_nonvacuous_eq
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
  apply StatMech.Walls.bku_route_nonvacuous ω L R hz₀ hz₁ hzne hno

/--
[bku_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkuassemble.lean)
-/
@[path]
private lemma bku_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) {S : Set (Site d)} [Fintype (↑S : Type)] [Nonempty (↑S : Type)] (G : SimpleGraph (↑S : Type)) [DecidableRel G.Adj], G.IsAcyclic → ∀ (ιU : Site d → (↑S : Type)), bku_armPathCarrier ω L R G ιU → (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R → bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z) → (∀ (F : SimpleGraph (↑S : Type)) [DecidableRel F.Adj], F ≤ G → F.IsAcyclic → (∀ v : (↑S : Type), F.degree v = 1 → bc121_Protected ω L R ιU v) → (∀ a b : (↑S : Type), bc121_Protected ω L R ιU a → bc121_Protected ω L R ιU b → G.Reachable a b → F.Reachable a b) → ∀ v : (↑S : Type), 1 ≤ F.degree v) → bc69_Gn_globalForest ω L R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a b : Site d), ¬ (bc67_contractedLattice ω L y).Reachable a b → ¬ ((bkt_ctrGraph ω L y).deleteIncidenceSet none).Reachable (some a) (some b)) ∧ (((SimpleGraph.fromEdgeSet {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet (0 : Fin 5)).Reachable 2 4) := by
-- proof
  apply StatMech.Walls.bku_status


-- created on 2026-10-23
