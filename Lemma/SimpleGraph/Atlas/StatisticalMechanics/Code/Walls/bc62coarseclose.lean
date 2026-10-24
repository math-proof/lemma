import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc62coarseclose
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc62_boxAround_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc62coarseclose.lean)
-/
@[path]
private lemma bc62_boxAround_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {L : ℕ}
  {y : Site d} :
-- imply
  bc61_boxAround d L (g • y) = (bc61_boxAround d L y).image (fun z => g • z) := by
-- proof
  apply StatMech.Walls.bc62_boxAround_shift g L y

/--
[bc62_removeSites_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc62coarseclose.lean)
-/
@[path]
private lemma bc62_removeSites_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  removeSites (T.image (fun z => g • z)) (shift g ω) = shift g (removeSites T ω) := by
-- proof
  apply StatMech.Walls.bc62_removeSites_shift g T ω

/--
[bc62_removeBox_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc62coarseclose.lean)
-/
@[path]
private lemma bc62_removeBox_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {L : ℕ}
  {y : Site d}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  removeSites (bc61_boxAround d L (g • y)) (shift g ω) = shift g (removeSites (bc61_boxAround d L y) ω) := by
-- proof
  apply StatMech.Walls.bc62_removeBox_shift g L y ω

/--
[bc62_isCoarseTrif_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc62coarseclose.lean)
-/
@[path]
private lemma bc62_isCoarseTrif_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d} :
-- imply
  bc61_IsCoarseTrifurcation (shift g ω) L (g • y) ↔ bc61_IsCoarseTrifurcation ω L y := by
-- proof
  apply StatMech.Walls.bc62_isCoarseTrif_shift g ω L y

/--
[bc62_measurable_removeSites](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc62coarseclose.lean)
-/
@[path]
private lemma bc62_measurable_removeSites_eq
  {d : ℕ}
  {T : Finset (Site d)} :
-- imply
  Measurable (fun ω : ConfigSpace (Sym2 (Site d)) => removeSites T ω) := by
-- proof
  apply StatMech.Walls.bc62_measurable_removeSites T

/--
[bc62_measurableSet_connected_removeSites](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc62coarseclose.lean)
-/
@[path]
private lemma bc62_measurableSet_connected_removeSites_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {a b : Site d} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | Connected d (removeSites T ω) a b} := by
-- proof
  apply StatMech.Walls.bc62_measurableSet_connected_removeSites T a b

/--
[bc62_measurableSet_clusterInfinite_removeSites](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc62coarseclose.lean)
-/
@[path]
private lemma bc62_measurableSet_clusterInfinite_removeSites_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {a : Site d} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | (cluster d (removeSites T ω) a).Infinite} := by
-- proof
  apply StatMech.Walls.bc62_measurableSet_clusterInfinite_removeSites T a

/--
[bc62_measurableSet_boxAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc62coarseclose.lean)
-/
@[path]
private lemma bc62_measurableSet_boxAdjacent_eq
  {d : ℕ}
  {L : ℕ}
  {y a : Site d} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | ∃ b ∈ bc61_boxAround d L y, (openSubgraph d ω).Adj b a} := by
-- proof
  apply StatMech.Walls.bc62_measurableSet_boxAdjacent L y a

/--
[bc62_measurableSet_coarseTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc62coarseclose.lean)
-/
@[path]
private lemma bc62_measurableSet_coarseTrif_eq
  {d : ℕ}
  {L : ℕ}
  {y : Site d} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | bc61_IsCoarseTrifurcation ω L y} := by
-- proof
  apply StatMech.Walls.bc62_measurableSet_coarseTrif L y

/--
[bc62_coarseTrifProb_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc62coarseclose.lean)
-/
@[path]
private lemma bc62_coarseTrifProb_const_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {L : ℕ}
  {y : Site d}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  μ {ω | bc61_IsCoarseTrifurcation ω L y} = μ {ω | bc61_IsCoarseTrifurcation ω L 0} := by
-- proof
  apply StatMech.Walls.bc62_coarseTrifProb_const μ hinv L y

/--
[bc62_coarseTcount_eq_sum_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc62coarseclose.lean)
-/
@[path]
private lemma bc62_coarseTcount_eq_sum_indicator_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ} :
-- imply
  (bc61_coarseTcount ω L R : ℝ≥0∞) = ∑ y ∈ boxFinsetBK d R, ({ω' | bc61_IsCoarseTrifurcation ω' L y}.indicator (fun _ => (1 : ℝ≥0∞))) ω := by
-- proof
  apply StatMech.Walls.bc62_coarseTcount_eq_sum_indicator ω L R

/--
[bc62_coarse_expectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc62coarseclose.lean)
-/
@[path]
private lemma bc62_coarse_expectation_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {L R : ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0} = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ := by
-- proof
  apply StatMech.Walls.bc62_coarse_expectation μ hinv L R

/--
[bc62_removeSites_forceOpen_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc62coarseclose.lean)
-/
@[path]
private lemma bc62_removeSites_forceOpen_eq_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {F : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hF : ∀ e ∈ F, ∃ t ∈ T, t ∈ e) :
-- imply
  removeSites T (forceOpenFinset F ω) = removeSites T ω := by
-- proof
  apply StatMech.Walls.bc62_removeSites_forceOpen_eq T F hF ω

/--
[bc62_isCoarseTrifurcation_of_neighbors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc62coarseclose.lean)
-/
@[path]
private lemma bc62_isCoarseTrifurcation_of_neighbors_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {a₁ a₂ a₃ b₁ b₂ b₃ : Site d}
-- given
  (hb1 : b₁ ∈ bc61_boxAround d L 0)
  (hb2 : b₂ ∈ bc61_boxAround d L 0)
  (hb3 : b₃ ∈ bc61_boxAround d L 0)
  (hadj1 : (hypercubicLattice d).Adj b₁ a₁)
  (hadj2 : (hypercubicLattice d).Adj b₂ a₂)
  (hadj3 : (hypercubicLattice d).Adj b₃ a₃)
  (hinf1 : (cluster d (removeSites (bc61_boxAround d L 0) ω) a₁).Infinite)
  (hinf2 : (cluster d (removeSites (bc61_boxAround d L 0) ω) a₂).Infinite)
  (hinf3 : (cluster d (removeSites (bc61_boxAround d L 0) ω) a₃).Infinite)
  (hsep12 : ¬ Connected d (removeSites (bc61_boxAround d L 0) ω) a₁ a₂)
  (hsep13 : ¬ Connected d (removeSites (bc61_boxAround d L 0) ω) a₁ a₃)
  (hsep23 : ¬ Connected d (removeSites (bc61_boxAround d L 0) ω) a₂ a₃) :
-- imply
  bc61_IsCoarseTrifurcation (forceOpenFinset {s(b₁, a₁), s(b₂, a₂), s(b₃, a₃)} ω) L 0 := by
-- proof
  apply StatMech.Walls.bc62_isCoarseTrifurcation_of_neighbors ω L a₁ a₂ a₃ b₁ b₂ b₃ hb1 hb2 hb3 hadj1 hadj2 hadj3 hinf1 hinf2 hinf3 hsep12 hsep13 hsep23

/--
[bc62_precursor_subset_force_coarseTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc62coarseclose.lean)
-/
@[path]
private lemma bc62_precursor_subset_force_coarseTrif_eq
  {d : ℕ}
  {L : ℕ}
  {a₁ a₂ a₃ b₁ b₂ b₃ : Site d} :
-- imply
  bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃ ⊆ (fun ω => forceOpenFinset {s(b₁, a₁), s(b₂, a₂), s(b₃, a₃)} ω) ⁻¹' {ω | bc61_IsCoarseTrifurcation ω L 0} := by
-- proof
  apply StatMech.Walls.bc62_precursor_subset_force_coarseTrif L a₁ a₂ a₃ b₁ b₂ b₃

/--
[bc62_coarseTrif_of_precursor_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc62coarseclose.lean)
-/
@[path]
private lemma bc62_coarseTrif_of_precursor_mem_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {a₁ a₂ a₃ b₁ b₂ b₃ : Site d}
-- given
  (hω : ω ∈ bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃) :
-- imply
  bc61_IsCoarseTrifurcation (forceOpenFinset {s(b₁, a₁), s(b₂, a₂), s(b₃, a₃)} ω) L 0 := by
-- proof
  apply StatMech.Walls.bc62_coarseTrif_of_precursor_mem ω L a₁ a₂ a₃ b₁ b₂ b₃ hω

/--
[bc62_coarseTrif_pos_of_precursor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc62coarseclose.lean)
-/
@[path]
private lemma bc62_coarseTrif_pos_of_precursor_pos_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
  {a₁ a₂ a₃ b₁ b₂ b₃ : Site d}
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hpos : 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
-- imply
  0 < μ {ω | bc61_IsCoarseTrifurcation ω L 0} := by
-- proof
  apply StatMech.Walls.bc62_coarseTrif_pos_of_precursor_pos μ hfe L a₁ a₂ a₃ b₁ b₂ b₃ hpos

/--
[bc62_coarseTrifExistence_of_route](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc62coarseclose.lean)
-/
@[path]
private lemma bc62_coarseTrifExistence_of_route_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
-- imply
  bc61_CoarseTrifExistence μ L := by
-- proof
  apply StatMech.Walls.bc62_coarseTrifExistence_of_route μ hfe L hcoarseRoute

/--
[bc62_boxVertex_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc62coarseclose.lean)
-/
@[path]
private lemma bc62_boxVertex_mem_eq
  {d : ℕ}
  {L : ℕ}
  {h : ℤ}
-- given
  (hh : 1 ≤ h)
  (hhL : h ≤ (L : ℤ)) :
-- imply
  bc57_pt (L : ℤ) h ∈ bc61_boxAround 2 L 0 := by
-- proof
  apply StatMech.Walls.bc62_boxVertex_mem hh hhL

/--
[bc62_upperLines_mem_coarsePrecursor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc62coarseclose.lean)
-/
@[path]
private lemma bc62_upperLines_mem_coarsePrecursor_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc60_upperLines ∈ bc62_CoarseTrifPrecursor 2 L (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt ((L : ℤ) + 1) 2) (bc57_pt ((L : ℤ) + 1) 3) (bc57_pt (L : ℤ) 1) (bc57_pt (L : ℤ) 2) (bc57_pt (L : ℤ) 3) := by
-- proof
  apply StatMech.Walls.bc62_upperLines_mem_coarsePrecursor hL

/--
[bc62_upperLines_forced_coarseTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc62coarseclose.lean)
-/
@[path]
private lemma bc62_upperLines_forced_coarseTrif_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc61_IsCoarseTrifurcation (forceOpenFinset {s(bc57_pt (L : ℤ) 1, bc57_pt ((L : ℤ) + 1) 1), s(bc57_pt (L : ℤ) 2, bc57_pt ((L : ℤ) + 1) 2), s(bc57_pt (L : ℤ) 3, bc57_pt ((L : ℤ) + 1) 3)} bc60_upperLines) L 0 := by
-- proof
  apply StatMech.Walls.bc62_upperLines_forced_coarseTrif hL

/--
[bc62_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc62coarseclose.lean)
-/
@[path]
private lemma bc62_status_eq
  {d : ℕ} :
-- imply
  (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))), IsTranslationInvariant (G := Multiplicative (Site 2)) μ → ∀ (L R : ℕ), ((boxFinsetBK 2 R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0} = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ) ∧ (∀ {L : ℕ}, 3 ≤ L → bc60_upperLines ∈ bc62_CoarseTrifPrecursor 2 L (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt ((L : ℤ) + 1) 2) (bc57_pt ((L : ℤ) + 1) 3) (bc57_pt (L : ℤ) 1) (bc57_pt (L : ℤ) 2) (bc57_pt (L : ℤ) 3)) := by
-- proof
  apply StatMech.Walls.bc62_status

/--
[bc62_infiniteClusters_top_null_of_forest_route](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc62coarseclose.lean)
-/
@[path]
private lemma bc62_infiniteClusters_top_null_of_forest_route_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc61_CoarseForestLeafCount ω L R)
  (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc62_infiniteClusters_top_null_of_forest_route μ hd hinv hfe L hforest hcoarseRoute


-- created on 2026-10-23
