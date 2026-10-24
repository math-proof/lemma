import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.TwoDim.ZhangLowerBound
open MeasureTheory Set Filter Topology StatMech StatMech.TwoDim


/--
[kzh_theta_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangLowerBound.lean)
-/
@[path]
private lemma kzh_theta_real_eq :
-- imply
  (percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one).toReal = halfMeasure.real (percolationEvent 2) := by
-- proof
  apply StatMech.TwoDim.kzh_theta_real

/--
[kzh_percProb_eq_zero_of_thetaReal_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangLowerBound.lean)
-/
@[path]
private lemma kzh_percProb_eq_zero_of_thetaReal_zero_eq
-- given
  (h : halfMeasure.real (percolationEvent 2) = 0) :
-- imply
  percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 := by
-- proof
  apply StatMech.TwoDim.kzh_percProb_eq_zero_of_thetaReal_zero h

/--
[kzh_crossing_to_one_of_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangLowerBound.lean)
-/
@[path]
private lemma kzh_crossing_to_one_of_union_eq
  {A B : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
-- given
  (hpa : PositivelyAssociated halfMeasure)
  (hAinc : ∀ n, IsIncreasing (A n))
  (hBinc : ∀ n, IsIncreasing (B n))
  (hAm : ∀ n, MeasurableSet (A n))
  (hBm : ∀ n, MeasurableSet (B n))
  (heq : ∀ n, halfMeasure.real (A n) = halfMeasure.real (B n))
  (hunion : Tendsto (fun n => halfMeasure.real (A n ∪ B n)) atTop (𝓝 1)) :
-- imply
  Tendsto (fun n => halfMeasure.real (A n)) atTop (𝓝 1) := by
-- proof
  apply StatMech.TwoDim.kzh_crossing_to_one_of_union hpa hAinc hBinc hAm hBm heq hunion

/--
[kzh_corLowerBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangLowerBound.lean)
-/
@[path]
private lemma kzh_corLowerBound_eq
  {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
  {A B : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
-- given
  (hpa : PositivelyAssociated halfMeasure)
  (hAinc : ∀ n, IsIncreasing (A n))
  (hBinc : ∀ n, IsIncreasing (B n))
  (hBm : ∀ n, MeasurableSet (B n))
  (hHm : ∀ n, MeasurableSet (A n))
  (hRmeas : Measurable R)
  (hRpres : Measure.map R halfMeasure = halfMeasure)
  (hdich : ∀ n, (A n)ᶜ = (R ∘ dualConfig) ⁻¹' (A n))
  (heq : ∀ n, halfMeasure.real (A n) = halfMeasure.real (B n))
  (hZhangUnion : BoxCrossingProperty halfMeasure 2 → 0 < halfMeasure.real (percolationEvent 2) → Tendsto (fun n => halfMeasure.real (A n ∪ B n)) atTop (𝓝 1)) :
-- imply
  BoxCrossingProperty halfMeasure 2 → percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 := by
-- proof
  apply StatMech.TwoDim.kzh_corLowerBound hpa hAinc hBinc hBm hHm hRmeas hRpres hdich heq hZhangUnion


-- created on 2026-10-23
