import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bfefiniteenergy
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bfe_coarseCount_eq_fineCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfefiniteenergy.lean)
-/
@[path]
private lemma bfe_coarseCount_eq_fineCount_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {R : ℕ} :
-- imply
  bc61_coarseTcount ω 0 R = (bfin2_trifSet_finite ω (R + 1)).toFinset.card := by
-- proof
  apply StatMech.Walls.bfe_coarseCount_eq_fineCount ω R

/--
[bfe_perConfig_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfefiniteenergy.lean)
-/
@[path]
private lemma bfe_perConfig_count_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {R : ℕ} :
-- imply
  bc61_coarseTcount ω 0 R ≤ boxSV_boundaryCard d (R + 1) := by
-- proof
  apply StatMech.Walls.bfe_perConfig_count ω R

/--
[bfe_exp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfefiniteenergy.lean)
-/
@[path]
private lemma bfe_exp_eq_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {R : ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω 0 0} = ∫⁻ ω, (bc61_coarseTcount ω 0 R : ℝ≥0∞) ∂μ := by
-- proof
  apply StatMech.Walls.bfe_exp_eq μ hinv R

/--
[bfe_expBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfefiniteenergy.lean)
-/
@[path]
private lemma bfe_expBound_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {R : ℕ} :
-- imply
  ∫⁻ ω, (bc61_coarseTcount ω 0 R : ℝ≥0∞) ∂μ ≤ (boxSV_boundaryCard d (R + 1) : ℝ≥0∞) := by
-- proof
  apply StatMech.Walls.bfe_expBound μ R

/--
[bfe_boxCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfefiniteenergy.lean)
-/
@[path]
private lemma bfe_boxCard_eq
  {d : ℕ}
  {R : ℕ} :
-- imply
  ((boxFinsetBK d R).card : ℝ) = (2 * (R : ℝ) + 1) ^ d := by
-- proof
  apply StatMech.Walls.bfe_boxCard R

/--
[bfe_amenability](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfefiniteenergy.lean)
-/
@[path]
private lemma bfe_amenability_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  Tendsto (fun R => (boxSV_boundaryCard d (R + 1) : ℝ) / ((boxFinsetBK d R).card : ℝ)) atTop (𝓝 0) := by
-- proof
  apply StatMech.Walls.bfe_amenability hd

/--
[bfe_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfefiniteenergy.lean)
-/
@[path]
private lemma bfe_dichotomy_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  μ {ω | bc61_IsCoarseTrifurcation ω 0 0} = 0 := by
-- proof
  apply StatMech.Walls.bfe_dichotomy hd μ hinv

/--
[bfe_top_null](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfefiniteenergy.lean)
-/
@[path]
private lemma bfe_top_null_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hexist : bc61_CoarseTrifExistence μ 0) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bfe_top_null hd μ hinv hexist

/--
[bfe_bk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfefiniteenergy.lean)
-/
@[path]
private lemma bfe_bk_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hexist : bc61_CoarseTrifExistence (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1) 0) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bfe_bk hd p hp1 hp0 hexist

/--
[bfe_bk_atLeastTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfefiniteenergy.lean)
-/
@[path]
private lemma bfe_bk_atLeastTwo_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hexist : bc61_CoarseTrifExistence (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1) 0) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 := by
-- proof
  apply StatMech.Walls.bfe_bk_atLeastTwo hd p hp1 hp0 hexist


-- created on 2026-10-23
