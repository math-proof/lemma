import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc63coarseforest.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc63_coarseArm_reaches_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc63coarseforest.lean)
-/
@[path]
private lemma bc63_coarseArm_reaches_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y a : Site d}
-- given
  (hR : 1 ≤ R)
  (habox : a ∈ box d R)
  (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
-- imply
  ∃ z ∈ vertexBoundary d R, Connected d (removeSites (bc61_boxAround d L y) ω) a z := by
-- proof
  apply StatMech.Walls.bc63_coarseArm_reaches_boundary ω L R hR y a habox hinf

/--
[bc63_coarseForest_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc63coarseforest.lean)
-/
@[path]
private lemma bc63_coarseForest_acyclic_eq
  {d : ℕ}
  [Fintype V]
  {G : SimpleGraph V} :
-- imply
  (osf_spanForest G).IsAcyclic := by
-- proof
  apply StatMech.Walls.bc63_coarseForest_acyclic G

/--
[bc63_subgraph_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc63coarseforest.lean)
-/
@[path]
private lemma bc63_subgraph_acyclic_eq
  {d : ℕ}
  [Fintype V]
  {G T : SimpleGraph V}
-- given
  (hsub : T ≤ osf_spanForest G) :
-- imply
  T.IsAcyclic := by
-- proof
  apply StatMech.Walls.bc63_subgraph_acyclic G T hsub

/--
[bc63_coarseForestLeafCount_discharges_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc63coarseforest.lean)
-/
@[path]
private lemma bc63_coarseForestLeafCount_discharges_count_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc61_CoarseForestLeafCount ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc63_coarseForestLeafCount_discharges_count ω L R h

/--
[bc63_coarseForestLeafCount_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc63coarseforest.lean)
-/
@[path]
private lemma bc63_coarseForestLeafCount_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁)
  (hno : ∀ y, y ∈ box d R → ¬ bc61_IsCoarseTrifurcation ω L y) :
-- imply
  bc61_CoarseForestLeafCount ω L R := by
-- proof
  apply StatMech.Walls.bc63_coarseForestLeafCount_of_noTrif ω L R hz₀ hz₁ hzne hno

/--
[bc63_coarseForestLeafCount_star](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc63coarseforest.lean)
-/
@[path]
private lemma bc63_coarseForestLeafCount_star_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {r : Site d}
  {z : Fin 3 → Site d}
-- given
  (_hrbox : r ∈ box d R)
  (_htri_r : bc61_IsCoarseTrifurcation ω L r)
  (hzb : ∀ i, z i ∈ vertexBoundary d R)
  (hzinj : Function.Injective z)
  (hsingle : ∀ y, y ∈ box d R → bc61_IsCoarseTrifurcation ω L y → y = r) :
-- imply
  bc61_CoarseForestLeafCount ω L R := by
-- proof
  apply StatMech.Walls.bc63_coarseForestLeafCount_star ω L R _hrbox _htri_r z hzb hzinj hsingle

/--
[bc63_coarseArmEmbedding_iff_forestLeafCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc63coarseforest.lean)
-/
@[path]
private lemma bc63_coarseArmEmbedding_iff_forestLeafCount_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ} :
-- imply
  bc63_CoarseArmEmbedding ω L R ↔ bc61_CoarseForestLeafCount ω L R := by
-- proof
  apply StatMech.Walls.bc63_coarseArmEmbedding_iff_forestLeafCount ω L R

/--
[bc63_coarseForestLeafCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc63coarseforest.lean)
-/
@[path]
private lemma bc63_coarseForestLeafCount_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc63_CoarseArmEmbedding ω L R) :
-- imply
  bc61_CoarseForestLeafCount ω L R := by
-- proof
  apply StatMech.Walls.bc63_coarseForestLeafCount ω L R h

/--
[bc63_coarseTcount_le_boundary_of_armEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc63coarseforest.lean)
-/
@[path]
private lemma bc63_coarseTcount_le_boundary_of_armEmbedding_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc63_CoarseArmEmbedding ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc63_coarseTcount_le_boundary_of_armEmbedding ω L R h

/--
[bc63_coarseArmEmbedding_star](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc63coarseforest.lean)
-/
@[path]
private lemma bc63_coarseArmEmbedding_star_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {r : Site d}
  {z : Fin 3 → Site d}
-- given
  (hrbox : r ∈ box d R)
  (htri_r : bc61_IsCoarseTrifurcation ω L r)
  (hzb : ∀ i, z i ∈ vertexBoundary d R)
  (hzinj : Function.Injective z)
  (hsingle : ∀ y, y ∈ box d R → bc61_IsCoarseTrifurcation ω L y → y = r) :
-- imply
  bc63_CoarseArmEmbedding ω L R := by
-- proof
  apply StatMech.Walls.bc63_coarseArmEmbedding_star ω L R hrbox htri_r z hzb hzinj hsingle

/--
[bc63_coarseRoute_of_precursor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc63coarseforest.lean)
-/
@[path]
private lemma bc63_coarseRoute_of_precursor_pos_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {L : ℕ}
  {a₁ a₂ a₃ b₁ b₂ b₃ : Site d}
-- given
  (hpre : 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
-- imply
  0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃) := by
-- proof
  apply StatMech.Walls.bc63_coarseRoute_of_precursor_pos μ L a₁ a₂ a₃ b₁ b₂ b₃ hpre

/--
[bc63_coarseTrifExistence_of_precursor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc63coarseforest.lean)
-/
@[path]
private lemma bc63_coarseTrifExistence_of_precursor_pos_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
  {a₁ a₂ a₃ b₁ b₂ b₃ : Site d}
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hpre : 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
-- imply
  bc61_CoarseTrifExistence μ L := by
-- proof
  apply StatMech.Walls.bc63_coarseTrifExistence_of_precursor_pos μ hfe L a₁ a₂ a₃ b₁ b₂ b₃ hpre

/--
[bc63_upperLines_arm_reaches_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc63coarseforest.lean)
-/
@[path]
private lemma bc63_upperLines_arm_reaches_boundary_eq
  {d : ℕ}
  {L R : ℕ}
  {h : ℤ}
-- given
  (hR : 1 ≤ R)
  (hh : 1 ≤ h)
  (hbox : bc57_pt ((L : ℤ) + 1) h ∈ box 2 R) :
-- imply
  ∃ z ∈ vertexBoundary 2 R, Connected 2 (removeSites (bc61_boxAround 2 L 0) bc60_upperLines) (bc57_pt ((L : ℤ) + 1) h) z := by
-- proof
  apply StatMech.Walls.bc63_upperLines_arm_reaches_boundary hR hh hbox

/--
[bc63_upperLines_coarsePrecursor_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc63coarseforest.lean)
-/
@[path]
private lemma bc63_upperLines_coarsePrecursor_nonempty_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc60_upperLines ∈ bc62_CoarseTrifPrecursor 2 L (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt ((L : ℤ) + 1) 2) (bc57_pt ((L : ℤ) + 1) 3) (bc57_pt (L : ℤ) 1) (bc57_pt (L : ℤ) 2) (bc57_pt (L : ℤ) 3) := by
-- proof
  apply StatMech.Walls.bc63_upperLines_coarsePrecursor_nonempty hL

/--
[bc63_upperLines_coarseTrifExistence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc63coarseforest.lean)
-/
@[path]
private lemma bc63_upperLines_coarseTrifExistence_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hpre : 0 < μ (bc62_CoarseTrifPrecursor 2 L (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt ((L : ℤ) + 1) 2) (bc57_pt ((L : ℤ) + 1) 3) (bc57_pt (L : ℤ) 1) (bc57_pt (L : ℤ) 2) (bc57_pt (L : ℤ) 3))) :
-- imply
  bc61_CoarseTrifExistence μ L := by
-- proof
  apply StatMech.Walls.bc63_upperLines_coarseTrifExistence μ hfe hpre

/--
[bc63_infiniteClusters_top_null_of_armEmbedding_route](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc63coarseforest.lean)
-/
@[path]
private lemma bc63_infiniteClusters_top_null_of_armEmbedding_route_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (harm : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc63_CoarseArmEmbedding ω L R)
  (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc63_infiniteClusters_top_null_of_armEmbedding_route μ hd hinv hfe L harm hcoarseRoute

/--
[bc63_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc63coarseforest.lean)
-/
@[path]
private lemma bc63_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 1 ≤ R → ∀ (y a : Site d), a ∈ box d R → (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite → ∃ z ∈ vertexBoundary d R, Connected d (removeSites (bc61_boxAround d L y) ω) a z) ∧ (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (osf_spanForest G).IsAcyclic) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc63_CoarseArmEmbedding ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) ∧ (∀ {L : ℕ}, 3 ≤ L → bc60_upperLines ∈ bc62_CoarseTrifPrecursor 2 L (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt ((L : ℤ) + 1) 2) (bc57_pt ((L : ℤ) + 1) 3) (bc57_pt (L : ℤ) 1) (bc57_pt (L : ℤ) 2) (bc57_pt (L : ℤ) 3)) := by
-- proof
  apply StatMech.Walls.bc63_status


-- created on 2026-10-23
