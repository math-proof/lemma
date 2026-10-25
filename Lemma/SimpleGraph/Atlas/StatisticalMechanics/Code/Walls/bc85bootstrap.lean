import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc85bootstrap
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc85_expectation_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc85bootstrap.lean)
-/
@[path]
private lemma bc85_expectation_identity_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {L R : ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0} = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ := by
-- proof
  apply StatMech.Walls.bc85_expectation_identity μ hinv L R

/--
[bc85_prob_zero_of_count_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc85bootstrap.lean)
-/
@[path]
private lemma bc85_prob_zero_of_count_forest_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hforest_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) :
-- imply
  μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 := by
-- proof
  apply StatMech.Walls.bc85_prob_zero_of_count_forest μ hd L hinv hforest_ae

/--
[bc85_exclude_infinite_N](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc85bootstrap.lean)
-/
@[path]
private lemma bc85_exclude_infinite_N_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (h0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0)
  (hexist : bc61_CoarseTrifExistence μ L) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc85_exclude_infinite_N μ L h0 hexist

/--
[bc85_dc_bootstrap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc85bootstrap.lean)
-/
@[path]
private lemma bc85_dc_bootstrap_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hforest_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R)
  (hexist : bc61_CoarseTrifExistence μ L) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc85_dc_bootstrap μ hd L hinv hforest_ae hexist

/--
[bc85_dc_bootstrap_of_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc85bootstrap.lean)
-/
@[path]
private lemma bc85_dc_bootstrap_of_leaf_eq
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
  apply StatMech.Walls.bc85_dc_bootstrap_of_leaf μ hd L hinv h0 hexist

/--
[bc85_dc_step1_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc85bootstrap.lean)
-/
@[path]
private lemma bc85_dc_step1_uniqueness_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hforest_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R)
  (hexist : bc61_CoarseTrifExistence μ L)
  (hmergeGeom : ∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 → ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k)) :
-- imply
  μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc85_dc_step1_uniqueness μ hd L herg hfe hinv hforest_ae hexist hmergeGeom

/--
[bc85_finiteN_iff_top_null](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc85bootstrap.lean)
-/
@[path]
private lemma bc85_finiteN_iff_top_null_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ] :
-- imply
  μ {ω | numInfiniteClusters d ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc85_finiteN_iff_top_null μ

/--
[bc85_count_on_finiteN_needs_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc85bootstrap.lean)
-/
@[path]
private lemma bc85_count_on_finiteN_needs_le_one_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
-- given
  (hN : numInfiniteClusters d ω ≤ 1)
  (h : bc61_IsCoarseTrifurcation ω L y) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, Connected d ω a₁ a₂ ∧ Connected d ω a₁ a₃ ∧ Connected d ω a₂ a₃ ∧ (¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂ ∧ ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₃ ∧ ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ a₃) := by
-- proof
  apply StatMech.Walls.bc85_count_on_finiteN_needs_le_one ω L hN h

/--
[bc85_finiteN_not_enough_note](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc85bootstrap.lean)
-/
@[path]
private lemma bc85_finiteN_not_enough_note_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) ∧ Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc76_yBuf L)) ∧ ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ := by
-- proof
  apply StatMech.Walls.bc85_finiteN_not_enough_note hL

/--
[bc85_bootstrap_noncircular_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc85bootstrap.lean)
-/
@[path]
private lemma bc85_bootstrap_noncircular_order_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  ((μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) → ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) ∧ ((μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) → bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters d ω = ⊤} = 0) := by
-- proof
  apply StatMech.Walls.bc85_bootstrap_noncircular_order μ L hinv

/--
[bc85_upperLines_N_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc85bootstrap.lean)
-/
@[path]
private lemma bc85_upperLines_N_top_eq
  {d : ℕ} :
-- imply
  numInfiniteClusters 2 bc60_upperLines = ⊤ := by
-- proof
  apply StatMech.Walls.bc85_upperLines_N_top

/--
[bc85_upperLines_null_of_bootstrap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc85bootstrap.lean)
-/
@[path]
private lemma bc85_upperLines_null_of_bootstrap_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
-- given
  (htop : μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) :
-- imply
  μ {ω : ConfigSpace (Sym2 (Site 2)) | ω = bc60_upperLines} = 0 := by
-- proof
  apply StatMech.Walls.bc85_upperLines_null_of_bootstrap μ htop

/--
[bc85_circularity_verdict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc85bootstrap.lean)
-/
@[path]
private lemma bc85_circularity_verdict_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  ((∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) → bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧ ((μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) → ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) ∧ (μ {ω | numInfiniteClusters d ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters d ω = ⊤} = 0) := by
-- proof
  apply StatMech.Walls.bc85_circularity_verdict μ hd L hinv

/--
[bc85_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc85bootstrap.lean)
-/
@[path]
private lemma bc85_status_eq
  {d : ℕ} :
-- imply
  (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ), IsTranslationInvariant (G := Multiplicative (Site 2)) μ → (∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) → bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ), IsErgodic (G := Multiplicative (Site 2)) μ → HasFiniteEnergyMerge μ → IsTranslationInvariant (G := Multiplicative (Site 2)) μ → (∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) → bc61_CoarseTrifExistence μ L → (∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters 2 ω = k} = 1 → ∃ F : Finset (Sym2 (Site 2)), 0 < μ (MergeWitness 2 F k)) → μ {ω | numInfiniteClusters 2 ω ≤ 1} = 1) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ], (μ {ω | numInfiniteClusters 2 ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters 2 ω = ⊤} = 0)) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y : Site 2), numInfiniteClusters 2 ω ≤ 1 → bc61_IsCoarseTrifurcation ω L y → ∃ a₁ a₂ a₃ : Site 2, Connected 2 ω a₁ a₂ ∧ Connected 2 ω a₁ a₃ ∧ Connected 2 ω a₂ a₃) ∧ (numInfiniteClusters 2 bc60_upperLines = ⊤) := by
-- proof
  apply StatMech.Walls.bc85_status


-- created on 2026-10-23
