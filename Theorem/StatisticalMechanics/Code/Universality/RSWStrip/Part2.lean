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
import Def.StatisticalMechanics.Code.Universality.RSWStrip
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip


theorem overlapConnectionEvent_isIncreasing (m m' c d : ℤ) (p q : Site 2)
    (hp : p ∈ rect m m' c d) (hq : q ∈ rect m m' c d) :
    IsIncreasing (overlapConnectionEvent m m' c d p q hp hq) := by
  intro ω ω' hωω' hω
  exact StatMech.TwoDim.connectedWithin_mono hωω' hω


theorem hvHalf_glue_subset {a m m' b c d : ℤ} (ham : a ≤ m) (hmm' : m ≤ m')
    (hm'b : m' ≤ b) {p q : Site 2}
    (hpO : p ∈ rect m m' c d) (hqO : q ∈ rect m m' c d)
    (hpL : p ∈ rect a m' c d) (hqR : q ∈ rect m b c d) :
    leftHalfCrossingEvent a m' c d p hpL
        ∩ overlapConnectionEvent m m' c d p q hpO hqO
        ∩ rightHalfCrossingEvent m b c d q hqR
      ⊆ horizontalCrossingEvent a b c d := by
  
  have _hoverlap : m ≤ m' := hmm'
  rintro ω ⟨⟨⟨xL, hc1⟩, hcV⟩, ⟨yR, hc2⟩⟩
  exact hv_glue ham hm'b xL.2 hpO hpL hc1 hqO hcV yR.2 hqR hc2


theorem rsw_strip_glue (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    [IsProbabilityMeasure μ] (hpa : PositivelyAssociated μ)
    {a m m' b c d : ℤ} (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    {p q : Site 2} (hpO : p ∈ rect m m' c d) (hqO : q ∈ rect m m' c d)
    (hpL : p ∈ rect a m' c d) (hqR : q ∈ rect m b c d) :
    μ.real (leftHalfCrossingEvent a m' c d p hpL)
        * μ.real (overlapConnectionEvent m m' c d p q hpO hqO)
        * μ.real (rightHalfCrossingEvent m b c d q hqR)
      ≤ μ.real (horizontalCrossingEvent a b c d) := by
  set A := leftHalfCrossingEvent a m' c d p hpL
  set B := overlapConnectionEvent m m' c d p q hpO hqO
  set C := rightHalfCrossingEvent m b c d q hqR
  have hA : IsIncreasing A := leftHalfCrossingEvent_isIncreasing a m' c d p hpL
  have hB : IsIncreasing B := overlapConnectionEvent_isIncreasing m m' c d p q hpO hqO
  have hC : IsIncreasing C := rightHalfCrossingEvent_isIncreasing m b c d q hqR
  have hsub : A ∩ B ∩ C ⊆ horizontalCrossingEvent a b c d :=
    hvHalf_glue_subset ham hmm' hm'b hpO hqO hpL hqR
  
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
