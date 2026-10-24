import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.BXPFromRSW
open Set MeasureTheory SimpleGraph StatMech StatMech.Universality


/--
[bxr_twoDim_horizontalCrossingEvent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPFromRSW.lean)
-/
@[path]
private lemma bxr_twoDim_horizontalCrossingEvent_eq_eq
  {a b : ℤ} :
-- imply
  StatMech.TwoDim.horizontalCrossingEvent a b = StatMech.RSW.Box.horizontalCrossingEvent 0 a 0 b := by
-- proof
  apply StatMech.Universality.bxr_twoDim_horizontalCrossingEvent_eq a b

/--
[bxr_twoDim_verticalCrossingEvent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPFromRSW.lean)
-/
@[path]
private lemma bxr_twoDim_verticalCrossingEvent_eq_eq
  {a b : ℤ} :
-- imply
  StatMech.TwoDim.verticalCrossingEvent a b = StatMech.RSW.Box.verticalCrossingEvent 0 a 0 b := by
-- proof
  apply StatMech.Universality.bxr_twoDim_verticalCrossingEvent_eq a b

/--
[bxr_translatedHorizontalCrossingEvent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPFromRSW.lean)
-/
@[path]
private lemma bxr_translatedHorizontalCrossingEvent_eq_eq
  {τ : Site 2}
  {a b : ℤ} :
-- imply
  translatedHorizontalCrossingEvent τ a b = translateConfig τ ⁻¹' StatMech.RSW.Box.horizontalCrossingEvent 0 a 0 b := by
-- proof
  apply StatMech.Universality.bxr_translatedHorizontalCrossingEvent_eq τ a b

/--
[bxr_translatedVerticalCrossingEvent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPFromRSW.lean)
-/
@[path]
private lemma bxr_translatedVerticalCrossingEvent_eq_eq
  {τ : Site 2}
  {a b : ℤ} :
-- imply
  translatedVerticalCrossingEvent τ a b = translateConfig τ ⁻¹' StatMech.RSW.Box.verticalCrossingEvent 0 a 0 b := by
-- proof
  apply StatMech.Universality.bxr_translatedVerticalCrossingEvent_eq τ a b

/--
[bxr_translatedHorizontalCrossing_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPFromRSW.lean)
-/
@[path]
private lemma bxr_translatedHorizontalCrossing_invariant_eq
  {τ : Site 2}
  {a b : ℤ}
-- given
  (hmeas : MeasurableSet (StatMech.RSW.Box.horizontalCrossingEvent 0 a 0 b)) :
-- imply
  rba_selfDualMeasure.real (translatedHorizontalCrossingEvent τ a b) = rba_selfDualMeasure.real (StatMech.RSW.Box.horizontalCrossingEvent 0 a 0 b) := by
-- proof
  apply StatMech.Universality.bxr_translatedHorizontalCrossing_invariant τ a b hmeas

/--
[bxr_translatedVerticalCrossing_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPFromRSW.lean)
-/
@[path]
private lemma bxr_translatedVerticalCrossing_invariant_eq
  {τ : Site 2}
  {a b : ℤ}
-- given
  (hmeas : MeasurableSet (StatMech.RSW.Box.verticalCrossingEvent 0 a 0 b)) :
-- imply
  rba_selfDualMeasure.real (translatedVerticalCrossingEvent τ a b) = rba_selfDualMeasure.real (StatMech.RSW.Box.verticalCrossingEvent 0 a 0 b) := by
-- proof
  apply StatMech.Universality.bxr_translatedVerticalCrossing_invariant τ a b hmeas

/--
[bxr_floor_natMul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPFromRSW.lean)
-/
@[path]
private lemma bxr_floor_natMul_eq
  {k0 n : ℕ} :
-- imply
  ⌊(k0 : ℝ) * (n : ℝ)⌋ = (k0 : ℤ) * (n : ℤ) := by
-- proof
  apply StatMech.Universality.bxr_floor_natMul k0 n

/--
[bxr_uniform_seed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPFromRSW.lean)
-/
@[path]
private lemma bxr_uniform_seed_eq
  {k0 : ℕ}
  {β γ : ℝ}
-- given
  (hpa : PositivelyAssociated rba_selfDualMeasure)
  (hk0 : 2 ≤ k0)
  (hβ : 0 < β)
  (hγ : 0 < γ)
  (hmeas2box : ∀ n : ℤ, 0 < n → MeasurableSet (horizontalCrossingEvent 0 (2 * n) 0 n))
  (hmeasband : ∀ n : ℤ, 0 < n → MeasurableSet (verticalCrossingEvent 0 n 0 n))
  (hmeasH : ∀ n : ℤ, 0 < n → MeasurableSet (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n))
  (hmeasV : ∀ n : ℤ, 0 < n → MeasurableSet (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n)))
  (hseed : ∀ n : ℤ, 0 < n → β ≤ rai_cross rba_selfDualMeasure n 1)
  (h2box : ∀ n : ℤ, 0 < n → γ ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
  (hband : ∀ n : ℤ, 0 < n → (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n))
  (hrefl : ∀ n : ℤ, 0 < n → rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n)) = rba_selfDualMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n)) :
-- imply
  (∀ (n : ℕ) (τ : Site 2), 1 ≤ n → β * ((1 / 2) * γ) ^ (k0 - 1) ≤ rba_selfDualMeasure.real (translatedHorizontalCrossingEvent τ ⌊(k0 : ℝ) * (n : ℝ)⌋ (n : ℤ))) ∧ (∀ (n : ℕ) (τ : Site 2), 1 ≤ n → β * ((1 / 2) * γ) ^ (k0 - 1) ≤ rba_selfDualMeasure.real (translatedVerticalCrossingEvent τ (n : ℤ) ⌊(k0 : ℝ) * (n : ℝ)⌋)) := by
-- proof
  apply StatMech.Universality.bxr_uniform_seed hpa hk0 hβ hγ hmeas2box hmeasband hmeasH hmeasV hseed h2box hband hrefl

/--
[bxr_boxCrossingProperty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPFromRSW.lean)
-/
@[path]
private lemma bxr_boxCrossingProperty_eq
  {k0 : ℕ}
  {β γ : ℝ}
-- given
  (hpa : PositivelyAssociated rba_selfDualMeasure)
  (hk0 : 2 ≤ k0)
  (hβ : 0 < β)
  (hγ : 0 < γ)
  (hmeas2box : ∀ n : ℤ, 0 < n → MeasurableSet (horizontalCrossingEvent 0 (2 * n) 0 n))
  (hmeasband : ∀ n : ℤ, 0 < n → MeasurableSet (verticalCrossingEvent 0 n 0 n))
  (hmeasH : ∀ n : ℤ, 0 < n → MeasurableSet (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n))
  (hmeasV : ∀ n : ℤ, 0 < n → MeasurableSet (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n)))
  (hseed : ∀ n : ℤ, 0 < n → β ≤ rai_cross rba_selfDualMeasure n 1)
  (h2box : ∀ n : ℤ, 0 < n → γ ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
  (hband : ∀ n : ℤ, 0 < n → (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n))
  (hrefl : ∀ n : ℤ, 0 < n → rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n)) = rba_selfDualMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n)) :
-- imply
  BoxCrossingProperty rba_selfDualMeasure (k0 : ℝ) := by
-- proof
  apply StatMech.Universality.bxr_boxCrossingProperty hpa hk0 hβ hγ hmeas2box hmeasband hmeasH hmeasV hseed h2box hband hrefl


-- created on 2026-10-23
