import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.belexpleaf.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bel_measurableSet_edgeOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/belexpleaf.lean)
-/
@[path]
private lemma bel_measurableSet_edgeOpen_eq
  {d : ℕ}
  {e : Sym2 (Site d)} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | ω e = true} := by
-- proof
  apply StatMech.Walls.bel_measurableSet_edgeOpen e

/--
[bel_leafOpenCount_eq_sum_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/belexpleaf.lean)
-/
@[path]
private lemma bel_leafOpenCount_eq_sum_indicator_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {F : Finset (Sym2 (Site d))} :
-- imply
  (bel_leafOpenCount F ω : ℝ≥0∞) = ∑ e ∈ F, ({ω' : ConfigSpace (Sym2 (Site d)) | ω' e = true}.indicator (fun _ => (1 : ℝ≥0∞))) ω := by
-- proof
  apply StatMech.Walls.bel_leafOpenCount_eq_sum_indicator ω F

/--
[bel_expLeaf_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/belexpleaf.lean)
-/
@[path]
private lemma bel_expLeaf_le_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {F : Finset (Sym2 (Site d))} :
-- imply
  ∫⁻ ω, (bel_leafOpenCount F ω : ℝ≥0∞) ∂μ ≤ (F.card : ℝ≥0∞) := by
-- proof
  apply StatMech.Walls.bel_expLeaf_le μ F

/--
[bel_top_null_of_forest_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/belexpleaf.lean)
-/
@[path]
private lemma bel_top_null_of_forest_open_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
  {F : ℕ → Finset (Sym2 (Site d))}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hd : 1 ≤ d)
  (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bpe_CoarseForestNoBnd ω L R (bel_leafOpenCount (F R) ω))
  (hdens : Filter.Tendsto (fun R => ((F R).card : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0))
  (hexist : bc61_CoarseTrifExistence μ L) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bel_top_null_of_forest_open μ hinv hd L F hforest hdens hexist

/--
[bel_bk_uniqueness_of_forest_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/belexpleaf.lean)
-/
@[path]
private lemma bel_bk_uniqueness_of_forest_open_eq
  {d : ℕ}
  {L : ℕ}
  {F : ℕ → Finset (Sym2 (Site d))}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bpe_CoarseForestNoBnd ω L R (bel_leafOpenCount (F R) ω))
  (hdens : Filter.Tendsto (fun R => ((F R).card : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0))
  (hcoarseRoute : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bel_bk_uniqueness_of_forest_open hd p hp1 hp0 L F hforest hdens hcoarseRoute

/--
[bel_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/belexpleaf.lean)
-/
@[path]
private lemma bel_status_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {F : ℕ → Finset (Sym2 (Site d))} :
-- imply
  (∀ R : ℕ, ∫⁻ ω, (bel_leafOpenCount (F R) ω : ℝ≥0∞) ∂μ ≤ ((F R).card : ℝ≥0∞)) ∧ (IsTranslationInvariant (G := Multiplicative (Site d)) μ → 1 ≤ d → ∀ L : ℕ, (∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bpe_CoarseForestNoBnd ω L R (bel_leafOpenCount (F R) ω)) → Filter.Tendsto (fun R => ((F R).card : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0) → bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters d ω = ⊤} = 0) := by
-- proof
  apply StatMech.Walls.bel_status μ F


-- created on 2026-10-23
