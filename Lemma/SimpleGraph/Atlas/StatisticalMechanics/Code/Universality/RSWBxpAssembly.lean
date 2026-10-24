import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.RSWBxpAssembly
open Set MeasureTheory SimpleGraph StatMech StatMech.Universality


/--
[rba_rsw_box_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWBxpAssembly.lean)
-/
@[path]
private lemma rba_rsw_box_crossing_eq
  {μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site 2)))}
  [MeasureTheory.IsProbabilityMeasure μ]
  {a m m' b c d : ℤ}
-- given
  (hpa : PositivelyAssociated μ)
  (ham : a ≤ m)
  (hmm' : m ≤ m')
  (hm'b : m' ≤ b)
  (hamL : a < m')
  (hmbR : m < b)
  (hcd : c ≤ d) :
-- imply
  μ.real (horizontalCrossingEvent a m' c d) * μ.real (verticalCrossingEvent m m' c d) * μ.real (horizontalCrossingEvent m b c d) ≤ μ.real (horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.rba_rsw_box_crossing μ hpa ham hmm' hm'b hamL hmbR hcd

/--
[rba_rsw_box_crossing_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWBxpAssembly.lean)
-/
@[path]
private lemma rba_rsw_box_crossing_chain_eq
  {μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site 2)))}
  [MeasureTheory.IsProbabilityMeasure μ]
  {a m m' b p e c d : ℤ}
-- given
  (hpa : PositivelyAssociated μ)
  (ham : a ≤ m)
  (hmm' : m ≤ m')
  (hm'b : m' ≤ b)
  (hamL : a < m')
  (hmbR : m < b)
  (hap : a ≤ p)
  (hpb : p ≤ b)
  (hbe : b ≤ e)
  (hab : a < b)
  (hpe : p < e)
  (hcd : c ≤ d) :
-- imply
  μ.real (horizontalCrossingEvent a m' c d) * μ.real (verticalCrossingEvent m m' c d) * μ.real (horizontalCrossingEvent m b c d) * μ.real (verticalCrossingEvent p b c d) * μ.real (horizontalCrossingEvent p e c d) ≤ μ.real (horizontalCrossingEvent a e c d) := by
-- proof
  apply StatMech.Universality.rba_rsw_box_crossing_chain μ hpa ham hmm' hm'b hamL hmbR hap hpb hbe hab hpe hcd

/--
[rba_sqrt_square_seed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWBxpAssembly.lean)
-/
@[path]
private lemma rba_sqrt_square_seed_eq
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
  1 - Real.sqrt (1 - s) ≤ μ.real (horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.rba_sqrt_square_seed μ hpa hmeasH hmeasV hsym hunion

/--
[rba_measurable_dualConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWBxpAssembly.lean)
-/
@[path]
private lemma rba_measurable_dualConfig_eq :
-- imply
  Measurable (dualConfig : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Universality.rba_measurable_dualConfig

/--
[rba_dualVerticalCrossing_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWBxpAssembly.lean)
-/
@[path]
private lemma rba_dualVerticalCrossing_eq_eq
  {a b c d : ℤ}
-- given
  (hmeasV : MeasurableSet (verticalCrossingEvent a b c d)) :
-- imply
  rba_selfDualMeasure.real (dualVerticalCrossingEvent a b c d) = rba_selfDualMeasure.real (verticalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.rba_dualVerticalCrossing_eq a b c d hmeasV

/--
[rba_dualHorizontalCrossing_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWBxpAssembly.lean)
-/
@[path]
private lemma rba_dualHorizontalCrossing_eq_eq
  {a b c d : ℤ}
-- given
  (hmeasH : MeasurableSet (horizontalCrossingEvent a b c d)) :
-- imply
  rba_selfDualMeasure.real (dualHorizontalCrossingEvent a b c d) = rba_selfDualMeasure.real (horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.rba_dualHorizontalCrossing_eq a b c d hmeasH

/--
[rba_self_dual_square_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWBxpAssembly.lean)
-/
@[path]
private lemma rba_self_dual_square_half_eq
  {n : ℤ}
-- given
  (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
  (hmeasV : MeasurableSet (verticalCrossingEvent 0 n 0 n))
  (hsep : (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n)
  (hsqsym : rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n) = rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n)) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
-- proof
  apply StatMech.Universality.rba_self_dual_square_half n hmeasH hmeasV hsep hsqsym

/--
[rba_glued_rectangle_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWBxpAssembly.lean)
-/
@[path]
private lemma rba_glued_rectangle_lower_bound_eq
  {μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site 2)))}
  [MeasureTheory.IsProbabilityMeasure μ]
  {a m m' b c d : ℤ}
  {v0 : ℝ}
-- given
  (hpa : PositivelyAssociated μ)
  (ham : a ≤ m)
  (hmm' : m ≤ m')
  (hm'b : m' ≤ b)
  (hamL : a < m')
  (hmbR : m < b)
  (hcd : c ≤ d)
  (hL : (1 : ℝ) / 2 ≤ μ.real (horizontalCrossingEvent a m' c d))
  (hR : (1 : ℝ) / 2 ≤ μ.real (horizontalCrossingEvent m b c d))
  (hVlb : v0 ≤ μ.real (verticalCrossingEvent m m' c d))
  (hv0 : 0 ≤ v0) :
-- imply
  v0 / 4 ≤ μ.real (horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.rba_glued_rectangle_lower_bound μ hpa ham hmm' hm'b hamL hmbR hcd hL hR hVlb hv0

/--
[rba_bxp_of_uniform_seed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWBxpAssembly.lean)
-/
@[path]
private lemma rba_bxp_of_uniform_seed_eq
  {μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site 2)))}
  {ρ : ℝ}
  {n0 : ℕ}
  {c : ℝ}
-- given
  (hρ : 1 < ρ)
  (hc : 0 < c)
  (hH : ∀ (n : ℕ) (τ : Site 2), n0 ≤ n → c ≤ μ.real (translatedHorizontalCrossingEvent τ ⌊ρ * (n : ℝ)⌋ (n : ℤ)))
  (hV : ∀ (n : ℕ) (τ : Site 2), n0 ≤ n → c ≤ μ.real (translatedVerticalCrossingEvent τ (n : ℤ) ⌊ρ * (n : ℝ)⌋)) :
-- imply
  BoxCrossingProperty μ ρ := by
-- proof
  apply StatMech.Universality.rba_bxp_of_uniform_seed μ ρ hρ n0 c hc hH hV


-- created on 2026-10-23
