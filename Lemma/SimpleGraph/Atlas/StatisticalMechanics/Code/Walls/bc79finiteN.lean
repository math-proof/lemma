import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc79finiteN
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc79_enat_012top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc79finiteN.lean)
-/
@[path]
private lemma bc79_enat_012top_eq
  {d : ℕ}
  {k : ℕ∞}
-- given
  (h : 2 ≤ k → k = ⊤) :
-- imply
  k = 0 ∨ k = 1 ∨ k = ⊤ := by
-- proof
  apply StatMech.Walls.bc79_enat_012top h

/--
[bc79_le_one_of_012top_ne_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc79finiteN.lean)
-/
@[path]
private lemma bc79_le_one_of_012top_ne_top_eq
  {d : ℕ}
  {k : ℕ∞}
-- given
  (h : k = 0 ∨ k = 1 ∨ k = ⊤)
  (hne : k ≠ ⊤) :
-- imply
  k ≤ 1 := by
-- proof
  apply StatMech.Walls.bc79_le_one_of_012top_ne_top h hne

/--
[bc79_merge_gives_only_012top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc79finiteN.lean)
-/
@[path]
private lemma bc79_merge_gives_only_012top_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {k : ℕ∞}
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hmergeGeom : ∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 → ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k))
  (hk : μ {ω | numInfiniteClusters d ω = k} = 1) :
-- imply
  k = 0 ∨ k = 1 ∨ k = ⊤ := by
-- proof
  apply StatMech.Walls.bc79_merge_gives_only_012top μ hfe hmergeGeom hk

/--
[bc79_finite_eq_top_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc79finiteN.lean)
-/
@[path]
private lemma bc79_finite_eq_top_compl_eq
  {d : ℕ} :
-- imply
  {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω < ⊤} = {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = ⊤}ᶜ := by
-- proof
  apply StatMech.Walls.bc79_finite_eq_top_compl

/--
[bc79_top_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc79finiteN.lean)
-/
@[path]
private lemma bc79_top_measurable_eq
  {d : ℕ} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = ⊤} := by
-- proof
  apply StatMech.Walls.bc79_top_measurable

/--
[bc79_finite_N_iff_top_null](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc79finiteN.lean)
-/
@[path]
private lemma bc79_finite_N_iff_top_null_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ] :
-- imply
  μ {ω | numInfiniteClusters d ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc79_finite_N_iff_top_null μ

/--
[bc79_finite_N_iff_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc79finiteN.lean)
-/
@[path]
private lemma bc79_finite_N_iff_le_one_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {k : ℕ∞}
-- given
  (hk : μ {ω | numInfiniteClusters d ω = k} = 1)
  (htri : k = 0 ∨ k = 1 ∨ k = ⊤) :
-- imply
  μ {ω | numInfiniteClusters d ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc79_finite_N_iff_le_one μ hk htri

/--
[bc79_finite_N_circular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc79finiteN.lean)
-/
@[path]
private lemma bc79_finite_N_circular_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {k : ℕ∞}
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hmergeGeom : ∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 → ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k))
  (hk : μ {ω | numInfiniteClusters d ω = k} = 1) :
-- imply
  (μ {ω | numInfiniteClusters d ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧ (μ {ω | numInfiniteClusters d ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters d ω ≤ 1} = 1) := by
-- proof
  apply StatMech.Walls.bc79_finite_N_circular μ hfe hmergeGeom hk

/--
[bc79_top_subset_atLeastTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc79finiteN.lean)
-/
@[path]
private lemma bc79_top_subset_atLeastTwo_eq
  {d : ℕ} :
-- imply
  {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = ⊤} ⊆ atLeastTwoInfinite d := by
-- proof
  apply StatMech.Walls.bc79_top_subset_atLeastTwo

/--
[bc79_top_null_of_merge_null](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc79finiteN.lean)
-/
@[path]
private lemma bc79_top_null_of_merge_null_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
-- given
  (hmerge : μ (atLeastTwoInfinite d) = 0) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc79_top_null_of_merge_null μ hmerge

/--
[bc79_merge_null_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc79finiteN.lean)
-/
@[path]
private lemma bc79_merge_null_iff_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))} :
-- imply
  μ (atLeastTwoInfinite d) = 0 ↔ μ {ω | 2 ≤ numInfiniteClusters d ω ∧ numInfiniteClusters d ω < ⊤} = 0 ∧ μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc79_merge_null_iff μ

/--
[bc79_directCount_is_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc79finiteN.lean)
-/
@[path]
private lemma bc79_directCount_is_forest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc73_SublatticeForest ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ (2 * L + 1) ^ d * boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc79_directCount_is_forest ω L R h

/--
[bc79_directCount_refuted_on_upperLines](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc79finiteN.lean)
-/
@[path]
private lemma bc79_directCount_refuted_on_upperLines_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) ∧ Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc76_yBuf L)) ∧ ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ := by
-- proof
  apply StatMech.Walls.bc79_directCount_refuted_on_upperLines hL

/--
[bc79_directCount_needs_gnCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc79finiteN.lean)
-/
@[path]
private lemma bc79_directCount_needs_gnCut_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  ((∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) → bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters d ω = ⊤} = 0) := by
-- proof
  apply StatMech.Walls.bc79_directCount_needs_gnCut μ hd L hinv

/--
[bc79_residue_noncircular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc79finiteN.lean)
-/
@[path]
private lemma bc79_residue_noncircular_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {L : ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (h0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) :
-- imply
  ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R := by
-- proof
  apply StatMech.Walls.bc79_residue_noncircular μ L hinv h0

/--
[bc79_bk_from_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc79finiteN.lean)
-/
@[path]
private lemma bc79_bk_from_leaf_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (h0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0)
  (hexist : bc61_CoarseTrifExistence μ L) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc79_bk_from_leaf μ hd L hinv h0 hexist

/--
[bc79_step1_from_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc79finiteN.lean)
-/
@[path]
private lemma bc79_step1_from_leaf_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (h0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0)
  (hexist : bc61_CoarseTrifExistence μ L)
  (hmergeGeom : ∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 → ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k)) :
-- imply
  μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc79_step1_from_leaf μ hd L herg hfe hinv h0 hexist hmergeGeom

/--
[bc79_top_null_of_forest_and_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc79finiteN.lean)
-/
@[path]
private lemma bc79_top_null_of_forest_and_le_one_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hle1 : μ {ω | numInfiniteClusters d ω ≤ 1} = 1) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc79_top_null_of_forest_and_le_one μ hle1

/--
[bc79_witness_top_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc79finiteN.lean)
-/
@[path]
private lemma bc79_witness_top_branch_eq
  {d : ℕ} :
-- imply
  numInfiniteClusters 2 bc60_upperLines = ⊤ := by
-- proof
  apply StatMech.Walls.bc79_witness_top_branch

/--
[bc79_cardinal_verdict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc79finiteN.lean)
-/
@[path]
private lemma bc79_cardinal_verdict_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
  {k : ℕ∞}
-- given
  (hd : 1 ≤ d)
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hmergeGeom : ∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 → ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k))
  (hk : μ {ω | numInfiniteClusters d ω = k} = 1) :
-- imply
  ((μ {ω | numInfiniteClusters d ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧ (μ {ω | numInfiniteClusters d ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters d ω ≤ 1} = 1)) ∧ ((μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) → bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters d ω ≤ 1} = 1) := by
-- proof
  apply StatMech.Walls.bc79_cardinal_verdict μ hd L herg hfe hinv hmergeGeom hk

/--
[bc79_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc79finiteN.lean)
-/
@[path]
private lemma bc79_status_eq
  {d : ℕ} :
-- imply
  (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ], (μ {ω | numInfiniteClusters 2 ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters 2 ω = ⊤} = 0)) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ], HasFiniteEnergyMerge μ → (∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters 2 ω = k} = 1 → ∃ F : Finset (Sym2 (Site 2)), 0 < μ (MergeWitness 2 F k)) → ∀ k : ℕ∞, μ {ω | numInfiniteClusters 2 ω = k} = 1 → k = 0 ∨ k = 1 ∨ k = ⊤) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ), IsErgodic (G := Multiplicative (Site 2)) μ → HasFiniteEnergyMerge μ → IsTranslationInvariant (G := Multiplicative (Site 2)) μ → μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 → bc61_CoarseTrifExistence μ L → (∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters 2 ω = k} = 1 → ∃ F : Finset (Sym2 (Site 2)), 0 < μ (MergeWitness 2 F k)) → μ {ω | numInfiniteClusters 2 ω ≤ 1} = 1) ∧ (numInfiniteClusters 2 bc60_upperLines = ⊤) := by
-- proof
  apply StatMech.Walls.bc79_status


-- created on 2026-10-23
