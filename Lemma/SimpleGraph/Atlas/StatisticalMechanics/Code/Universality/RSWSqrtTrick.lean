import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWSqrtTrick
open Set MeasureTheory SimpleGraph StatMech StatMech.Universality


/--
[rst_selfDual_box_crossing_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSqrtTrick.lean)
-/
@[path]
private lemma rst_selfDual_box_crossing_half_eq
  {a b c d : ℤ}
-- given
  (hmeasH : MeasurableSet (horizontalCrossingEvent a b c d))
  (hmeasV : MeasurableSet (verticalCrossingEvent a b c d))
  (hsep : (horizontalCrossingEvent a b c d)ᶜ ⊆ dualVerticalCrossingEvent a b c d)
  (hsqsym : rba_selfDualMeasure.real (verticalCrossingEvent a b c d) = rba_selfDualMeasure.real (horizontalCrossingEvent a b c d)) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.rst_selfDual_box_crossing_half a b c d hmeasH hmeasV hsep hsqsym

/--
[rst_square_crossing_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSqrtTrick.lean)
-/
@[path]
private lemma rst_square_crossing_half_eq
  {n : ℤ}
-- given
  (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
  (hmeasV : MeasurableSet (verticalCrossingEvent 0 n 0 n))
  (hsep : (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n)
  (hsqsym : rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n) = rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n)) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
-- proof
  apply StatMech.Universality.rst_square_crossing_half n hmeasH hmeasV hsep hsqsym

/--
[rst_square_vertical_crossing_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSqrtTrick.lean)
-/
@[path]
private lemma rst_square_vertical_crossing_half_eq
  {n : ℤ}
-- given
  (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
  (hmeasV : MeasurableSet (verticalCrossingEvent 0 n 0 n))
  (hsep : (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n)
  (hsqsym : rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n) = rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n)) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n) := by
-- proof
  apply StatMech.Universality.rst_square_vertical_crossing_half n hmeasH hmeasV hsep hsqsym

/--
[rst_rectangle_crossing_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSqrtTrick.lean)
-/
@[path]
private lemma rst_rectangle_crossing_pos_eq
  {μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site 2)))}
  [MeasureTheory.IsProbabilityMeasure μ]
  {n : ℤ}
  {v0 : ℝ}
-- given
  (hpa : PositivelyAssociated μ)
  (hn : 0 < n)
  (hL : (1 : ℝ) / 2 ≤ μ.real (horizontalCrossingEvent 0 n 0 n))
  (hR : (1 : ℝ) / 2 ≤ μ.real (horizontalCrossingEvent n (2 * n) 0 n))
  (hVlb : v0 ≤ μ.real (verticalCrossingEvent n n 0 n))
  (hv0 : 0 ≤ v0) :
-- imply
  v0 / 4 ≤ μ.real (horizontalCrossingEvent 0 (2 * n) 0 n) := by
-- proof
  apply StatMech.Universality.rst_rectangle_crossing_pos μ hpa hn hL hR hVlb hv0

/--
[rst_selfDual_rectangle_crossing_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSqrtTrick.lean)
-/
@[path]
private lemma rst_selfDual_rectangle_crossing_pos_eq
  {n : ℤ}
  {v0 : ℝ}
-- given
  (hpa : PositivelyAssociated rba_selfDualMeasure)
  (hn : 0 < n)
  (hmeasHL : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
  (hmeasVL : MeasurableSet (verticalCrossingEvent 0 n 0 n))
  (hsepL : (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n)
  (hsqsymL : rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n) = rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n))
  (hmeasHR : MeasurableSet (horizontalCrossingEvent n (2 * n) 0 n))
  (hmeasVR : MeasurableSet (verticalCrossingEvent n (2 * n) 0 n))
  (hsepR : (horizontalCrossingEvent n (2 * n) 0 n)ᶜ ⊆ dualVerticalCrossingEvent n (2 * n) 0 n)
  (hsqsymR : rba_selfDualMeasure.real (verticalCrossingEvent n (2 * n) 0 n) = rba_selfDualMeasure.real (horizontalCrossingEvent n (2 * n) 0 n))
  (hVlb : v0 ≤ rba_selfDualMeasure.real (verticalCrossingEvent n n 0 n))
  (hv0 : 0 ≤ v0) :
-- imply
  v0 / 4 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n) := by
-- proof
  apply StatMech.Universality.rst_selfDual_rectangle_crossing_pos hpa hn hmeasHL hmeasVL hsepL hsqsymL hmeasHR hmeasVR hsepR hsqsymR hVlb hv0


-- created on 2026-10-23
