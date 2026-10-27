import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWConstantMaintenance
open Set MeasureTheory SimpleGraph StatMech StatMech.Universality


/--
[rcm_aspect_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConstantMaintenance.lean)
-/
@[path]
private lemma rcm_aspect_step_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {a m m' b c d : ℤ}
  {cL cR : ℝ}
-- given
  (hpa : PositivelyAssociated μ)
  (ham : a ≤ m)
  (hmm' : m ≤ m')
  (hm'b : m' ≤ b)
  (hamL : a < m')
  (hmbR : m < b)
  (hcd : c ≤ d)
  (hcL0 : 0 ≤ cL)
  (hcR0 : 0 ≤ cR)
  (hL : cL ≤ μ.real (horizontalCrossingEvent a m' c d))
  (hR : cR ≤ μ.real (horizontalCrossingEvent m b c d))
  (hVlb : (1 : ℝ) / 2 ≤ μ.real (verticalCrossingEvent m m' c d)) :
-- imply
  cL * (1 / 2) * cR ≤ μ.real (horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.rcm_aspect_step μ hpa ham hmm' hm'b hamL hmbR hcd hcL0 hcR0 hL hR hVlb

/--
[rcm_aspect_step_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConstantMaintenance.lean)
-/
@[path]
private lemma rcm_aspect_step_pos_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {a m m' b c d : ℤ}
  {cL cR : ℝ}
-- given
  (hpa : PositivelyAssociated μ)
  (ham : a ≤ m)
  (hmm' : m ≤ m')
  (hm'b : m' ≤ b)
  (hamL : a < m')
  (hmbR : m < b)
  (hcd : c ≤ d)
  (hcL : 0 < cL)
  (hcR : 0 < cR)
  (hL : cL ≤ μ.real (horizontalCrossingEvent a m' c d))
  (hR : cR ≤ μ.real (horizontalCrossingEvent m b c d))
  (hVlb : (1 : ℝ) / 2 ≤ μ.real (verticalCrossingEvent m m' c d)) :
-- imply
  0 < μ.real (horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.rcm_aspect_step_pos μ hpa ham hmm' hm'b hamL hmbR hcd hcL hcR hL hR hVlb

/--
[rcm_aspect_step_selfDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConstantMaintenance.lean)
-/
@[path]
private lemma rcm_aspect_step_selfDual_eq
  {a m m' b c d : ℤ}
  {cL cR : ℝ}
-- given
  (hpa : PositivelyAssociated rba_selfDualMeasure)
  (ham : a ≤ m)
  (hmm' : m ≤ m')
  (hm'b : m' ≤ b)
  (hamL : a < m')
  (hmbR : m < b)
  (hcd : c ≤ d)
  (hcL0 : 0 ≤ cL)
  (hcR0 : 0 ≤ cR)
  (hL : cL ≤ rba_selfDualMeasure.real (horizontalCrossingEvent a m' c d))
  (hR : cR ≤ rba_selfDualMeasure.real (horizontalCrossingEvent m b c d))
  (hmeasHB : MeasurableSet (horizontalCrossingEvent m m' c d))
  (hmeasVB : MeasurableSet (verticalCrossingEvent m m' c d))
  (hsepB : (horizontalCrossingEvent m m' c d)ᶜ ⊆ dualVerticalCrossingEvent m m' c d)
  (hsqsymB : rba_selfDualMeasure.real (verticalCrossingEvent m m' c d) = rba_selfDualMeasure.real (horizontalCrossingEvent m m' c d)) :
-- imply
  cL * (1 / 2) * cR ≤ rba_selfDualMeasure.real (horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.rcm_aspect_step_selfDual hpa ham hmm' hm'b hamL hmbR hcd hcL0 hcR0 hL hR hmeasHB hmeasVB hsepB hsqsymB


-- created on 2026-10-23
