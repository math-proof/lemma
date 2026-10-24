import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.KestenBXPWire
open MeasureTheory Set Filter Topology StatMech StatMech.Universality


/--
[kbw_halfMeasure_eq_rba](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenBXPWire.lean)
-/
@[path]
private lemma kbw_halfMeasure_eq_rba_eq :
-- imply
  halfMeasure = rba_selfDualMeasure := by
-- proof
  apply StatMech.Universality.kbw_halfMeasure_eq_rba

/--
[kbw_bxp_half_faithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenBXPWire.lean)
-/
@[path]
private lemma kbw_bxp_half_faithful_eq
  {ρ : ℝ}
-- given
  (hpa : PositivelyAssociated rba_selfDualMeasure)
  (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b → MeasurableSet (horizontalCrossingEvent 0 a 0 b))
  (hmeasGenV : ∀ a b : ℤ, 0 < a → 0 < b → MeasurableSet (verticalCrossingEvent 0 a 0 b))
  (hmeasFace : ∀ n : ℤ, 0 < n → MeasurableSet (crr_FaceRectVerticalEvent n))
  (hmeasThin : ∀ n : ℤ, 0 < n → MeasurableSet (horizontalCrossingEvent (-1) n 0 (n - 1)))
  (h2box : ∀ n : ℤ, 0 < n → (1 : ℝ) / 8 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
  (hρ : 1 < ρ) :
-- imply
  BoxCrossingProperty halfMeasure ρ := by
-- proof
  apply StatMech.Universality.kbw_bxp_half_faithful hpa hmeasGenH hmeasGenV hmeasFace hmeasThin h2box ρ hρ

/--
[kbw_bxp_half_supplied](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenBXPWire.lean)
-/
@[path]
private lemma kbw_bxp_half_supplied_eq
  {β γ : ℝ}
  {ρ : ℝ}
-- given
  (hpa : PositivelyAssociated rba_selfDualMeasure)
  (hβ : 0 < β)
  (hγ : 0 < γ)
  (hmeas2box : ∀ n : ℤ, 0 < n → MeasurableSet (horizontalCrossingEvent 0 (2 * n) 0 n))
  (hmeasband : ∀ n : ℤ, 0 < n → MeasurableSet (verticalCrossingEvent 0 n 0 n))
  (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b → MeasurableSet (horizontalCrossingEvent 0 a 0 b))
  (hmeasGenV : ∀ a b : ℤ, 0 < a → 0 < b → MeasurableSet (verticalCrossingEvent 0 a 0 b))
  (hseed : ∀ n : ℤ, 0 < n → β ≤ rai_cross rba_selfDualMeasure n 1)
  (h2box : ∀ n : ℤ, 0 < n → γ ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
  (hband : ∀ n : ℤ, 0 < n → (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n))
  (hrefl : ∀ (k0 : ℕ), 2 ≤ k0 → ∀ n : ℤ, 0 < n → rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n)) = rba_selfDualMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n))
  (hρ : 1 < ρ) :
-- imply
  BoxCrossingProperty halfMeasure ρ := by
-- proof
  apply StatMech.Universality.kbw_bxp_half_supplied hpa hβ hγ hmeas2box hmeasband hmeasGenH hmeasGenV hseed h2box hband hrefl ρ hρ

/--
[kbw_kesten_bxp_supplied](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenBXPWire.lean)
-/
@[path]
private lemma kbw_kesten_bxp_supplied_eq
  {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
  {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
  {β γ : ℝ}
-- given
  (hpa : PositivelyAssociated rba_selfDualMeasure)
  (hβ : 0 < β)
  (hγ : 0 < γ)
  (hmeas2box : ∀ n : ℤ, 0 < n → MeasurableSet (horizontalCrossingEvent 0 (2 * n) 0 n))
  (hmeasband : ∀ n : ℤ, 0 < n → MeasurableSet (verticalCrossingEvent 0 n 0 n))
  (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b → MeasurableSet (horizontalCrossingEvent 0 a 0 b))
  (hmeasGenV : ∀ a b : ℤ, 0 < a → 0 < b → MeasurableSet (verticalCrossingEvent 0 a 0 b))
  (hseed : ∀ n : ℤ, 0 < n → β ≤ rai_cross rba_selfDualMeasure n 1)
  (h2box : ∀ n : ℤ, 0 < n → γ ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
  (hband : ∀ n : ℤ, 0 < n → (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n))
  (hrefl : ∀ (k0 : ℕ), 2 ≤ k0 → ∀ n : ℤ, 0 < n → rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n)) = rba_selfDualMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n))
  (hCorLowerBound : BoxCrossingProperty halfMeasure 2 → percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0)
  (hHm : ∀ n, MeasurableSet (boxFam n))
  (hRmeas : Measurable R)
  (hRpres : Measure.map R halfMeasure = halfMeasure)
  (hdich : ∀ n, (boxFam n)ᶜ = (R ∘ dualConfig) ⁻¹' (boxFam n))
  (hSharpThreshold : ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < criticalProbability 2 → Tendsto (fun n => (bernoulliProductMeasure p hp).real (boxFam n)) atTop (𝓝 0)) :
-- imply
  criticalProbability 2 = 1 / 2 := by
-- proof
  apply StatMech.Universality.kbw_kesten_bxp_supplied hpa hβ hγ hmeas2box hmeasband hmeasGenH hmeasGenV hseed h2box hband hrefl hCorLowerBound hHm hRmeas hRpres hdich hSharpThreshold

/--
[kbw_criticalProbability_le_half_square_faithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenBXPWire.lean)
-/
@[path]
private lemma kbw_criticalProbability_le_half_square_faithful_eq
-- given
  (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b → MeasurableSet (horizontalCrossingEvent 0 a 0 b))
  (hmeasFace : ∀ n : ℤ, 0 < n → MeasurableSet (crr_FaceRectVerticalEvent n))
  (hmeasThin : ∀ n : ℤ, 0 < n → MeasurableSet (horizontalCrossingEvent (-1) n 0 (n - 1))) :
-- imply
  criticalProbability 2 ≤ 1 / 2 := by
-- proof
  apply StatMech.Universality.kbw_criticalProbability_le_half_square_faithful hmeasGenH hmeasFace hmeasThin

/--
[kbw_kesten_square_faithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenBXPWire.lean)
-/
@[path]
private lemma kbw_kesten_square_faithful_eq
-- given
  (hpa : PositivelyAssociated rba_selfDualMeasure)
  (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b → MeasurableSet (horizontalCrossingEvent 0 a 0 b))
  (hmeasGenV : ∀ a b : ℤ, 0 < a → 0 < b → MeasurableSet (verticalCrossingEvent 0 a 0 b))
  (hmeasFace : ∀ n : ℤ, 0 < n → MeasurableSet (crr_FaceRectVerticalEvent n))
  (hmeasThin : ∀ n : ℤ, 0 < n → MeasurableSet (horizontalCrossingEvent (-1) n 0 (n - 1)))
  (h2box : ∀ n : ℤ, 0 < n → (1 : ℝ) / 8 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
  (hCorLowerBound : BoxCrossingProperty halfMeasure 2 → percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0) :
-- imply
  criticalProbability 2 = 1 / 2 := by
-- proof
  apply StatMech.Universality.kbw_kesten_square_faithful hpa hmeasGenH hmeasGenV hmeasFace hmeasThin h2box hCorLowerBound

/--
[kbw_kesten_no_percolation_supplied](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenBXPWire.lean)
-/
@[path]
private lemma kbw_kesten_no_percolation_supplied_eq
  {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
  {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
  {β γ : ℝ}
-- given
  (hpa : PositivelyAssociated rba_selfDualMeasure)
  (hβ : 0 < β)
  (hγ : 0 < γ)
  (hmeas2box : ∀ n : ℤ, 0 < n → MeasurableSet (horizontalCrossingEvent 0 (2 * n) 0 n))
  (hmeasband : ∀ n : ℤ, 0 < n → MeasurableSet (verticalCrossingEvent 0 n 0 n))
  (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b → MeasurableSet (horizontalCrossingEvent 0 a 0 b))
  (hmeasGenV : ∀ a b : ℤ, 0 < a → 0 < b → MeasurableSet (verticalCrossingEvent 0 a 0 b))
  (hseed : ∀ n : ℤ, 0 < n → β ≤ rai_cross rba_selfDualMeasure n 1)
  (h2box : ∀ n : ℤ, 0 < n → γ ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
  (hband : ∀ n : ℤ, 0 < n → (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n))
  (hrefl : ∀ (k0 : ℕ), 2 ≤ k0 → ∀ n : ℤ, 0 < n → rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n)) = rba_selfDualMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n))
  (hCorLowerBound : BoxCrossingProperty halfMeasure 2 → percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0)
  (hHm : ∀ n, MeasurableSet (boxFam n))
  (hRmeas : Measurable R)
  (hRpres : Measure.map R halfMeasure = halfMeasure)
  (hdich : ∀ n, (boxFam n)ᶜ = (R ∘ dualConfig) ⁻¹' (boxFam n))
  (hSharpThreshold : ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < criticalProbability 2 → Tendsto (fun n => (bernoulliProductMeasure p hp).real (boxFam n)) atTop (𝓝 0)) :
-- imply
  criticalProbability 2 = 1 / 2 ∧ percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 := by
-- proof
  apply StatMech.Universality.kbw_kesten_no_percolation_supplied hpa hβ hγ hmeas2box hmeasband hmeasGenH hmeasGenV hseed h2box hband hrefl hCorLowerBound hHm hRmeas hRpres hdich hSharpThreshold


-- created on 2026-10-23
