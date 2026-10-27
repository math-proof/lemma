import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWBandBound
open Set MeasureTheory SimpleGraph StatMech StatMech.Universality


/--
[rbb_band_crossing_lb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWBandBound.lean)
-/
@[path]
private lemma rbb_band_crossing_lb_eq
  {a b c d : ℤ}
-- given
  (hmeasH : MeasurableSet (horizontalCrossingEvent a b c d))
  (hmeasV : MeasurableSet (verticalCrossingEvent a b c d))
  (hsep : (horizontalCrossingEvent a b c d)ᶜ ⊆ dualVerticalCrossingEvent a b c d)
  (hsqsym : rba_selfDualMeasure.real (verticalCrossingEvent a b c d) = rba_selfDualMeasure.real (horizontalCrossingEvent a b c d)) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.rbb_band_crossing_lb a b c d hmeasH hmeasV hsep hsqsym

/--
[rbb_band_crossing_sqrt_lb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWBandBound.lean)
-/
@[path]
private lemma rbb_band_crossing_sqrt_lb_eq
  {μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site 2)))}
  [MeasureTheory.IsProbabilityMeasure μ]
  {a b c d : ℤ}
  {s : ℝ}
-- given
  (hpa : PositivelyAssociated μ)
  (hmeasH : MeasurableSet (horizontalCrossingEvent a b c d))
  (hmeasV : MeasurableSet (verticalCrossingEvent a b c d))
  (hsym : μ.real (verticalCrossingEvent a b c d) = μ.real (horizontalCrossingEvent a b c d))
  (hunion : s ≤ μ.real (horizontalCrossingEvent a b c d ∪ verticalCrossingEvent a b c d)) :
-- imply
  1 - Real.sqrt (1 - s) ≤ μ.real (verticalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.rbb_band_crossing_sqrt_lb μ hpa hmeasH hmeasV hsym hunion

/--
[rbb_rectangle_crossing_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWBandBound.lean)
-/
@[path]
private lemma rbb_rectangle_crossing_uniform_eq
  {a m m' b c d : ℤ}
-- given
  (hpa : PositivelyAssociated rba_selfDualMeasure)
  (ham : a ≤ m)
  (hmm' : m ≤ m')
  (hm'b : m' ≤ b)
  (hamL : a < m')
  (hmbR : m < b)
  (hcd : c ≤ d)
  (hL : (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent a m' c d))
  (hR : (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent m b c d))
  (hmeasHB : MeasurableSet (horizontalCrossingEvent m m' c d))
  (hmeasVB : MeasurableSet (verticalCrossingEvent m m' c d))
  (hsepB : (horizontalCrossingEvent m m' c d)ᶜ ⊆ dualVerticalCrossingEvent m m' c d)
  (hsqsymB : rba_selfDualMeasure.real (verticalCrossingEvent m m' c d) = rba_selfDualMeasure.real (horizontalCrossingEvent m m' c d)) :
-- imply
  (1 : ℝ) / 8 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.rbb_rectangle_crossing_uniform hpa ham hmm' hm'b hamL hmbR hcd hL hR hmeasHB hmeasVB hsepB hsqsymB


-- created on 2026-10-23
