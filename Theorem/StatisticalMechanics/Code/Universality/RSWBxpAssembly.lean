/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWBxpAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Universality.RSWStrip.Part3
import Theorem.StatisticalMechanics.Code.Universality.G3PercDualityFull.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip


theorem rba_rsw_box_crossing
    (μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site 2))))
    [MeasureTheory.IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) {a m m' b c d : ℤ}
    (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hamL : a < m') (hmbR : m < b) (hcd : c ≤ d) :
    μ.real (horizontalCrossingEvent a m' c d)
        * μ.real (verticalCrossingEvent m m' c d)
        * μ.real (horizontalCrossingEvent m b c d)
      ≤ μ.real (horizontalCrossingEvent a b c d) :=
  StatMech.Lattice.jec_rsw_strip_glue μ hpa ham hmm' hm'b hamL hmbR hcd


theorem rba_rsw_box_crossing_chain
    (μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site 2))))
    [MeasureTheory.IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) {a m m' b p e c d : ℤ}
    (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hamL : a < m') (hmbR : m < b)
    (hap : a ≤ p) (hpb : p ≤ b) (hbe : b ≤ e) (hab : a < b) (hpe : p < e) (hcd : c ≤ d) :
    μ.real (horizontalCrossingEvent a m' c d)
        * μ.real (verticalCrossingEvent m m' c d)
        * μ.real (horizontalCrossingEvent m b c d)
        * μ.real (verticalCrossingEvent p b c d)
        * μ.real (horizontalCrossingEvent p e c d)
      ≤ μ.real (horizontalCrossingEvent a e c d) := by
  have hinner := StatMech.Lattice.jec_rsw_strip_glue μ hpa ham hmm' hm'b hamL hmbR hcd
  have houter := StatMech.Lattice.jec_rsw_strip_glue μ hpa hap hpb hbe hab hpe hcd
  have hVnn : (0 : ℝ) ≤ μ.real (verticalCrossingEvent p b c d) := measureReal_nonneg
  have hHnn : (0 : ℝ) ≤ μ.real (horizontalCrossingEvent p e c d) := measureReal_nonneg
  calc μ.real (horizontalCrossingEvent a m' c d)
        * μ.real (verticalCrossingEvent m m' c d)
        * μ.real (horizontalCrossingEvent m b c d)
        * μ.real (verticalCrossingEvent p b c d)
        * μ.real (horizontalCrossingEvent p e c d)
      = (μ.real (horizontalCrossingEvent a m' c d)
          * μ.real (verticalCrossingEvent m m' c d)
          * μ.real (horizontalCrossingEvent m b c d))
        * μ.real (verticalCrossingEvent p b c d)
        * μ.real (horizontalCrossingEvent p e c d) := by ring
    _ ≤ μ.real (horizontalCrossingEvent a b c d)
        * μ.real (verticalCrossingEvent p b c d)
        * μ.real (horizontalCrossingEvent p e c d) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hinner hVnn) hHnn
    _ ≤ μ.real (horizontalCrossingEvent a e c d) := houter


theorem rba_sqrt_square_seed
    (μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site 2))))
    [MeasureTheory.IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) {a b c d : ℤ} {s : ℝ}
    (hmeasH : MeasurableSet (horizontalCrossingEvent a b c d))
    (hmeasV : MeasurableSet (verticalCrossingEvent a b c d))
    (hsym : μ.real (verticalCrossingEvent a b c d)
              = μ.real (horizontalCrossingEvent a b c d))
    (hunion : s ≤ μ.real (horizontalCrossingEvent a b c d ∪ verticalCrossingEvent a b c d)) :
    1 - Real.sqrt (1 - s) ≤ μ.real (horizontalCrossingEvent a b c d) := by
  have h := rsw_sqrt_trick_eq μ hpa
    (horizontalCrossingEvent_isIncreasing a b c d)
    (verticalCrossingEvent_isIncreasing a b c d)
    hmeasH hmeasV hsym.symm
  have hmono :
      Real.sqrt (1 - μ.real (horizontalCrossingEvent a b c d ∪ verticalCrossingEvent a b c d))
        ≤ Real.sqrt (1 - s) := Real.sqrt_le_sqrt (by linarith)
  linarith


end Universality
end StatMech
