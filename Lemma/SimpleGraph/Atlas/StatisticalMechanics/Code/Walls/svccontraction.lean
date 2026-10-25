import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.svccontraction
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[svc_gap1_discharged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/svccontraction.lean)
-/
@[path]
private lemma svc_gap1_discharged_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (hd : 1 ≤ d)
  (hL : 3 ≤ L) :
-- imply
  bc112_SeparatedArmGraph ω L R := by
-- proof
  apply StatMech.Walls.svc_gap1_discharged hd ω L R hL

/--
[svc_full_separated_iff_gap2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/svccontraction.lean)
-/
@[path]
private lemma svc_full_separated_iff_gap2_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ} :
-- imply
  bc112_BoundaryLeafResidue ω L R ↔ bc106_SeparatedContractedTrifGraph ω L R := by
-- proof
  apply StatMech.Walls.svc_full_separated_iff_gap2 ω L R

/--
[svc_full_separated_of_gap1_and_boundaryLeaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/svccontraction.lean)
-/
@[path]
private lemma svc_full_separated_of_gap1_and_boundaryLeaf_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {S : Set (Site d)}
  {G : SimpleGraph (↑S : Type)}
  {ιU : Site d → (↑S : Type)}
-- given
  (hSfin : Fintype (↑S : Type))
  (hSne : Nonempty (↑S : Type))
  (hGdec : DecidableRel G.Adj)
  (hFdec : DecidableRel (osf_spanForest G).Adj)
  (hnbr : ∀ y, y ∈ box d R → bc106_SeparatedCoarseTrif ω L y → ∃ v₁ v₂ v₃ : (↑S : Type), G.Adj (ιU y) v₁ ∧ G.Adj (ιU y) v₂ ∧ G.Adj (ιU y) v₃ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable v₁ v₂ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable v₁ v₃ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable v₂ v₃)
  (hιinj : ∀ y, y ∈ box d R → bc106_SeparatedCoarseTrif ω L y → ∀ z, z ∈ box d R → bc106_SeparatedCoarseTrif ω L z → ιU y = ιU z → y = z)
  (hmin : ∀ v, 1 ≤ (osf_spanForest G).degree v)
  (hleaf : ∀ v : (↑S : Type), (osf_spanForest G).degree v = 1 → (v : Site d) ∈ vertexBoundary d R) :
-- imply
  bc106_SeparatedContractedTrifGraph ω L R := by
-- proof
  apply StatMech.Walls.svc_full_separated_of_gap1_and_boundaryLeaf ω L R hSfin hSne G hGdec hFdec ιU hnbr hιinj hmin hleaf

/--
[svc_separated_count_le_boundary_of_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/svccontraction.lean)
-/
@[path]
private lemma svc_separated_count_le_boundary_of_full_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc106_SeparatedContractedTrifGraph ω L R) :
-- imply
  bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.svc_separated_count_le_boundary_of_full ω L R h

/--
[svc_count_absorbs_sharing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/svccontraction.lean)
-/
@[path]
private lemma svc_count_absorbs_sharing_eq
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
  apply StatMech.Walls.svc_count_absorbs_sharing G hacyc hmin

/--
[svc_origin_event_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/svccontraction.lean)
-/
@[path]
private lemma svc_origin_event_eq_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ} :
-- imply
  bc106_SeparatedCoarseTrif ω L (0 : Site d) ↔ bc61_IsCoarseTrifurcation ω L (0 : Site d) := by
-- proof
  apply StatMech.Walls.svc_origin_event_eq ω L

/--
[svc_separated_drives_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/svccontraction.lean)
-/
@[path]
private lemma svc_separated_drives_dichotomy_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hexp : ∀ R : ℕ, ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0} = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
  (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc73_SublatticeForest ω L R)
  (hexist : bc61_CoarseTrifExistence μ L) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.svc_separated_drives_dichotomy μ hd L hexp hforest hexist

/--
[svc_horn_A_leaf_in_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/svccontraction.lean)
-/
@[path]
private lemma svc_horn_A_leaf_in_box_eq
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
  apply StatMech.Walls.svc_horn_A_leaf_in_box hd hL y hk

/--
[svc_horn_incompatibility](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/svccontraction.lean)
-/
@[path]
private lemma svc_horn_incompatibility_eq
  {d : ℕ} :
-- imply
  ((SimpleGraph.fromEdgeSet {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet (0 : Fin 5)).Reachable 2 4 := by
-- proof
  apply StatMech.Walls.svc_horn_incompatibility

/--
[svc_horn_incompatibility_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/svccontraction.lean)
-/
@[path]
private lemma svc_horn_incompatibility_connected_eq
  {d : ℕ} :
-- imply
  (SimpleGraph.fromEdgeSet {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).Reachable 1 4 := by
-- proof
  apply StatMech.Walls.svc_horn_incompatibility_connected

/--
[svc_withinHub_boundary_targets](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/svccontraction.lean)
-/
@[path]
private lemma svc_withinHub_boundary_targets_eq
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
  ∃ z₁ z₂ z₃ : Site d, (z₁ ∈ vertexBoundary d R ∧ z₂ ∈ vertexBoundary d R ∧ z₃ ∈ vertexBoundary d R) ∧ (z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃) := by
-- proof
  apply StatMech.Walls.svc_withinHub_boundary_targets ω L R hR y a₁ a₂ a₃ hb₁ hb₂ hb₃ hi₁ hi₂ hi₃ hc₁₂ hc₁₃ hc₂₃

/--
[svc_bk_top_null_of_gap2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/svccontraction.lean)
-/
@[path]
private lemma svc_bk_top_null_of_gap2_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hexp : ∀ R : ℕ, ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0} = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
  (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc73_SublatticeForest ω L R)
  (hexist : bc61_CoarseTrifExistence μ L) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.svc_bk_top_null_of_gap2 μ hd L hexp hforest hexist

/--
[svc_bk_uniqueness_of_gap2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/svccontraction.lean)
-/
@[path]
private lemma svc_bk_uniqueness_of_gap2_eq
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
  apply StatMech.Walls.svc_bk_uniqueness_of_gap2 hd p hp1 hp0 L hGlobal hcoarseRoute

/--
[svc_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/svccontraction.lean)
-/
@[path]
private lemma svc_nonvacuous_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ : Site d}
-- given
  (hno : ∀ y, y ∈ box d R → ¬ bc106_SeparatedCoarseTrif ω L y) :
-- imply
  bc112_SeparatedArmGraph ω L R := by
-- proof
  apply StatMech.Walls.svc_nonvacuous ω L R hno

/--
[svc_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/svccontraction.lean)
-/
@[path]
private lemma svc_status_eq
  {d : ℕ} :
-- imply
  (∀ (hd : 1 ≤ d) (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 3 ≤ L → bc112_SeparatedArmGraph ω L R) ∧ (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj], G.IsAcyclic → (∀ v, 1 ≤ G.degree v) → (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc112_BoundaryLeafResidue ω L R ↔ bc106_SeparatedContractedTrifGraph ω L R) ∧ (∀ (hd : 1 ≤ d) (L : ℕ), 3 ≤ L → ∀ (y : Site d) {k : ℤ}, k ∈ bc112_shifts → bc112_leaf hd y k ∈ bc61_boxAround d L y) ∧ (((SimpleGraph.fromEdgeSet {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet (0 : Fin 5)).Reachable 2 4) := by
-- proof
  apply StatMech.Walls.svc_status


-- created on 2026-10-23
