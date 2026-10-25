/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.Strip.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
import Def.StatisticalMechanics.Code.Universality.RSWStrip.Part2
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip


theorem rsw_strip_glue_of_intersection (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    [IsProbabilityMeasure μ] (hpa : PositivelyAssociated μ)
    {a m m' b c d : ℤ}
    (hint : ∀ ω, HVIntersectionProperty ω a m m' b c d) :
    μ.real (horizontalCrossingEvent a m' c d)
        * μ.real (verticalCrossingEvent m m' c d)
        * μ.real (horizontalCrossingEvent m b c d)
      ≤ μ.real (horizontalCrossingEvent a b c d) := by
  set A := horizontalCrossingEvent a m' c d
  set B := verticalCrossingEvent m m' c d
  set C := horizontalCrossingEvent m b c d
  have hA : IsIncreasing A := horizontalCrossingEvent_isIncreasing a m' c d
  have hB : IsIncreasing B := verticalCrossingEvent_isIncreasing m m' c d
  have hC : IsIncreasing C := horizontalCrossingEvent_isIncreasing m b c d
  have hsub : A ∩ B ∩ C ⊆ horizontalCrossingEvent a b c d := by
    rintro ω ⟨⟨hAω, hBω⟩, hCω⟩
    exact hint ω hAω hBω hCω
  have h1 : μ.real A * μ.real B ≤ μ.real (A ∩ B) := hpa A B hA hB
  have h2 : μ.real (A ∩ B) * μ.real C ≤ μ.real (A ∩ B ∩ C) :=
    hpa (A ∩ B) C (hA.inter hB) hC
  have hnn : (0 : ℝ) ≤ μ.real C := measureReal_nonneg
  calc μ.real A * μ.real B * μ.real C
      ≤ μ.real (A ∩ B) * μ.real C := mul_le_mul_of_nonneg_right h1 hnn
    _ ≤ μ.real (A ∩ B ∩ C) := h2
    _ ≤ μ.real (horizontalCrossingEvent a b c d) := measureReal_mono hsub

end Universality
end StatMech
