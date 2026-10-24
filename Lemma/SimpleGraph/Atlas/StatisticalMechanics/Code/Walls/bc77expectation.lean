import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc77expectation
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc77_expected_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc77expectation.lean)
-/
@[path]
private lemma bc77_expected_count_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {L R : ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0} = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ := by
-- proof
  apply StatMech.Walls.bc77_expected_count μ hinv L R

/--
[bc77_coarseTrif_prob_eq_zero_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc77expectation.lean)
-/
@[path]
private lemma bc77_coarseTrif_prob_eq_zero_ae_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
  {bdry : ℕ → ℕ}
-- given
  (hexp : ∀ R : ℕ, ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0} = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
  (hbound_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc61_coarseTcount ω L R ≤ bdry R)
  (hvol : ∀ R, 0 < (boxFinsetBK d R).card)
  (hdens : Filter.Tendsto (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0)) :
-- imply
  μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 := by
-- proof
  apply StatMech.Walls.bc77_coarseTrif_prob_eq_zero_ae μ L bdry hexp hbound_ae hvol hdens

/--
[bc77_top_null_of_ae_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc77expectation.lean)
-/
@[path]
private lemma bc77_top_null_of_ae_bound_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
  {bdry : ℕ → ℕ}
-- given
  (hexp : ∀ R : ℕ, ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0} = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
  (hbound_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc61_coarseTcount ω L R ≤ bdry R)
  (hvol : ∀ R, 0 < (boxFinsetBK d R).card)
  (hdens : Filter.Tendsto (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0))
  (hexist : bc61_CoarseTrifExistence μ L) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc77_top_null_of_ae_bound μ L bdry hexp hbound_ae hvol hdens hexist

/--
[bc77_ae_bound_of_ae_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc77expectation.lean)
-/
@[path]
private lemma bc77_ae_bound_of_ae_forest_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {L : ℕ}
-- given
  (hforest_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) :
-- imply
  ∀ R : ℕ, ∀ᵐ ω ∂μ, bc61_coarseTcount ω L R ≤ (2 * L + 1) ^ d * boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc77_ae_bound_of_ae_forest μ L hforest_ae

/--
[bc77_top_null_of_ae_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc77expectation.lean)
-/
@[path]
private lemma bc77_top_null_of_ae_forest_eq
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
  apply StatMech.Walls.bc77_top_null_of_ae_forest μ hd L hinv hforest_ae hexist

/--
[bc77_ae_forest_iff_bad_null](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc77expectation.lean)
-/
@[path]
private lemma bc77_ae_forest_iff_bad_null_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {L R : ℕ}
-- given
  (hmeas : MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | ¬ bc73_SublatticeForest ω L R}) :
-- imply
  (∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) ↔ μ {ω : ConfigSpace (Sym2 (Site d)) | ¬ bc73_SublatticeForest ω L R} = 0 := by
-- proof
  apply StatMech.Walls.bc77_ae_forest_iff_bad_null μ L R hmeas

/--
[bc77_top_null_of_bad_null](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc77expectation.lean)
-/
@[path]
private lemma bc77_top_null_of_bad_null_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hmeasbad : ∀ R : ℕ, MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | ¬ bc73_SublatticeForest ω L R})
  (hbadnull : ∀ R : ℕ, μ {ω : ConfigSpace (Sym2 (Site d)) | ¬ bc73_SublatticeForest ω L R} = 0)
  (hexist : bc61_CoarseTrifExistence μ L) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc77_top_null_of_bad_null μ hd L hinv hmeasbad hbadnull hexist

/--
[bc77_upperLines_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc77expectation.lean)
-/
@[path]
private lemma bc77_upperLines_singleton_eq
  {d : ℕ} :
-- imply
  ({bc60_upperLines} : Set (ConfigSpace (Sym2 (Site 2)))) = {ω | ω = bc60_upperLines} := by
-- proof
  apply StatMech.Walls.bc77_upperLines_singleton

/--
[bc77_upperLines_null_of_singleton_null](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc77expectation.lean)
-/
@[path]
private lemma bc77_upperLines_null_of_singleton_null_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
-- given
  (h0 : μ {bc60_upperLines} = 0) :
-- imply
  μ {ω : ConfigSpace (Sym2 (Site 2)) | ω = bc60_upperLines} = 0 := by
-- proof
  apply StatMech.Walls.bc77_upperLines_null_of_singleton_null μ h0

/--
[bc77_circularity_note](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc77expectation.lean)
-/
@[path]
private lemma bc77_circularity_note_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  ((∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) → bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧ (∀ R : ℕ, MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | ¬ bc73_SublatticeForest ω L R} → ((∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) ↔ μ {ω : ConfigSpace (Sym2 (Site d)) | ¬ bc73_SublatticeForest ω L R} = 0)) := by
-- proof
  apply StatMech.Walls.bc77_circularity_note μ hd L hinv

/--
[bc77_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc77expectation.lean)
-/
@[path]
private lemma bc77_status_eq
  {d : ℕ} :
-- imply
  (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ) (bdry : ℕ → ℕ), (∀ R : ℕ, ((boxFinsetBK 2 R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0} = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ) → (∀ R : ℕ, ∀ᵐ ω ∂μ, bc61_coarseTcount ω L R ≤ bdry R) → (∀ R, 0 < (boxFinsetBK 2 R).card) → Filter.Tendsto (fun R => (bdry R : ℝ) / ((boxFinsetBK 2 R).card : ℝ)) Filter.atTop (nhds 0) → bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ), IsTranslationInvariant (G := Multiplicative (Site 2)) μ → (∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) → bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧ (({bc60_upperLines} : Set (ConfigSpace (Sym2 (Site 2)))) = {ω | ω = bc60_upperLines}) := by
-- proof
  apply StatMech.Walls.bc77_status


-- created on 2026-10-23
