import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.BXPMinimalHyp
open Set MeasureTheory SimpleGraph StatMech StatMech.Universality


/--
[bmh_square_reflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPMinimalHyp.lean)
-/
@[path]
private lemma bmh_square_reflection_eq
  {n : ℤ}
-- given
  (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n)) :
-- imply
  rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n) = rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
-- proof
  apply StatMech.Universality.bmh_square_reflection n hmeasH

/--
[bmh_square_seed_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPMinimalHyp.lean)
-/
@[path]
private lemma bmh_square_seed_half_eq
  {n : ℤ}
-- given
  (_hn : 0 < n)
  (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
  (hmeasV : MeasurableSet (verticalCrossingEvent 0 n 0 n))
  (hsep : (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n) :
-- imply
  (1 : ℝ) / 2 ≤ rai_cross rba_selfDualMeasure n 1 := by
-- proof
  apply StatMech.Universality.bmh_square_seed_half n _hn hmeasH hmeasV hsep

/--
[bmh_band_seed_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPMinimalHyp.lean)
-/
@[path]
private lemma bmh_band_seed_half_eq
  {n : ℤ}
-- given
  (_hn : 0 < n)
  (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
  (hmeasV : MeasurableSet (verticalCrossingEvent 0 n 0 n))
  (hsep : (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n) := by
-- proof
  apply StatMech.Universality.bmh_band_seed_half n _hn hmeasH hmeasV hsep

/--
[bmh_square_seed_half_faithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPMinimalHyp.lean)
-/
@[path]
private lemma bmh_square_seed_half_faithful_eq
  {n : ℤ}
-- given
  (hn : 0 < n)
  (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
  (hmeasFace : MeasurableSet (crr_FaceRectVerticalEvent n))
  (hmeasThin : MeasurableSet (horizontalCrossingEvent (-1) n 0 (n - 1))) :
-- imply
  (1 : ℝ) / 2 ≤ rai_cross rba_selfDualMeasure n 1 := by
-- proof
  apply StatMech.Universality.bmh_square_seed_half_faithful n hn hmeasH hmeasFace hmeasThin

/--
[bmh_band_seed_half_faithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPMinimalHyp.lean)
-/
@[path]
private lemma bmh_band_seed_half_faithful_eq
  {n : ℤ}
-- given
  (hn : 0 < n)
  (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
  (hmeasFace : MeasurableSet (crr_FaceRectVerticalEvent n))
  (hmeasThin : MeasurableSet (horizontalCrossingEvent (-1) n 0 (n - 1))) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n) := by
-- proof
  apply StatMech.Universality.bmh_band_seed_half_faithful n hn hmeasH hmeasFace hmeasThin

/--
[bmh_boxCrossingProperty_selfDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPMinimalHyp.lean)
-/
@[path]
private lemma bmh_boxCrossingProperty_selfDual_eq
-- given
  (hpa : PositivelyAssociated rba_selfDualMeasure)
  (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b → MeasurableSet (horizontalCrossingEvent 0 a 0 b))
  (hmeasGenV : ∀ a b : ℤ, 0 < a → 0 < b → MeasurableSet (verticalCrossingEvent 0 a 0 b))
  (hsepSquare : ∀ n : ℤ, 0 < n → (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n)
  (h2box : ∀ n : ℤ, 0 < n → (1 : ℝ) / 8 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n)) :
-- imply
  ∀ ρ : ℝ, 1 < ρ → BoxCrossingProperty rba_selfDualMeasure ρ := by
-- proof
  apply StatMech.Universality.bmh_boxCrossingProperty_selfDual hpa hmeasGenH hmeasGenV hsepSquare h2box

/--
[bmh_boxCrossingProperty_selfDual_faithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPMinimalHyp.lean)
-/
@[path]
private lemma bmh_boxCrossingProperty_selfDual_faithful_eq
-- given
  (hpa : PositivelyAssociated rba_selfDualMeasure)
  (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b → MeasurableSet (horizontalCrossingEvent 0 a 0 b))
  (hmeasGenV : ∀ a b : ℤ, 0 < a → 0 < b → MeasurableSet (verticalCrossingEvent 0 a 0 b))
  (hmeasFace : ∀ n : ℤ, 0 < n → MeasurableSet (crr_FaceRectVerticalEvent n))
  (hmeasThin : ∀ n : ℤ, 0 < n → MeasurableSet (horizontalCrossingEvent (-1) n 0 (n - 1)))
  (h2box : ∀ n : ℤ, 0 < n → (1 : ℝ) / 8 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n)) :
-- imply
  ∀ ρ : ℝ, 1 < ρ → BoxCrossingProperty rba_selfDualMeasure ρ := by
-- proof
  apply StatMech.Universality.bmh_boxCrossingProperty_selfDual_faithful hpa hmeasGenH hmeasGenV hmeasFace hmeasThin h2box


-- created on 2026-10-23
