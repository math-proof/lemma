/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean -/

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
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
import Def.StatisticalMechanics.Code.RSW.Strip
open Set MeasureTheory SimpleGraph


namespace StatMech

namespace RSW

namespace Strip

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.Universality


theorem leftHalfCrossingEvent_isIncreasing (a m c d : ℤ) (z : Site 2)
    (hz : z ∈ rect a m c d) :
    IsIncreasing (leftHalfCrossingEvent a m c d z hz) := by
  intro ω ω' hωω' hω
  obtain ⟨xL, hc⟩ := hω
  exact ⟨xL, StatMech.TwoDim.connectedWithin_mono hωω' hc⟩


theorem rightHalfCrossingEvent_isIncreasing (m b c d : ℤ) (z : Site 2)
    (hz : z ∈ rect m b c d) :
    IsIncreasing (rightHalfCrossingEvent m b c d z hz) := by
  intro ω ω' hωω' hω
  obtain ⟨yR, hc⟩ := hω
  exact ⟨yR, StatMech.TwoDim.connectedWithin_mono hωω' hc⟩


theorem halfCrossing_glue_subset {a m b c d : ℤ} (ham : a ≤ m) (hmb : m ≤ b)
    {z : Site 2} (hz0 : z 0 = m) (hzc : c ≤ z 1) (hzd : z 1 ≤ d) :
    leftHalfCrossingEvent a m c d z
        (rightSide_subset (mem_shared_column ham hmb hz0 hzc hzd).1)
      ∩ rightHalfCrossingEvent m b c d z
        (leftSide_subset (mem_shared_column ham hmb hz0 hzc hzd).2)
      ⊆ horizontalCrossingEvent a b c d := by
  rintro ω ⟨⟨xL, hc1⟩, ⟨yR, hc2⟩⟩
  obtain ⟨hzR1, hzL2⟩ := mem_shared_column ham hmb hz0 hzc hzd
  exact horizontalCrossing_glue_of_meet ham hmb xL.2 hz0 hzc hzd hc1 yR.2 hc2


theorem measureReal_horizontalCrossing_ge_halves {a m b c d : ℤ}
    (ham : a ≤ m) (hmb : m ≤ b) {z : Site 2} (hz0 : z 0 = m) (hzc : c ≤ z 1)
    (hzd : z 1 ≤ d) (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsFiniteMeasure μ]
    (hpa : PositivelyAssociated μ) :
    μ.real (leftHalfCrossingEvent a m c d z
          (rightSide_subset (mem_shared_column ham hmb hz0 hzc hzd).1))
        * μ.real (rightHalfCrossingEvent m b c d z
          (leftSide_subset (mem_shared_column ham hmb hz0 hzc hzd).2))
      ≤ μ.real (horizontalCrossingEvent a b c d) :=
  measureReal_glue_ge_mul μ hpa
    (leftHalfCrossingEvent_isIncreasing a m c d z _)
    (rightHalfCrossingEvent_isIncreasing m b c d z _)
    (halfCrossing_glue_subset ham hmb hz0 hzc hzd)


theorem measureReal_chain_ge_prod {ι : Type*} {E : Type*}
    (μ : Measure (ConfigSpace E)) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) (s : Finset ι)
    {A : ι → Set (ConfigSpace E)} (hA : ∀ i, IsIncreasing (A i))
    {C : Set (ConfigSpace E)} (hsub : (⋂ i ∈ s, A i) ⊆ C) :
    (∏ i ∈ s, μ.real (A i)) ≤ μ.real C := by
  classical
  induction s using Finset.induction generalizing C with
  | empty =>
      
      simp only [Finset.prod_empty]
      have huniv : (Set.univ : Set (ConfigSpace E)) ⊆ C := by
        simpa using hsub
      have hC : C = Set.univ := Set.eq_univ_of_univ_subset huniv
      subst hC
      simp [measureReal_def]
  | insert i s hi ih =>
      
      rw [Finset.prod_insert hi]
      
      have hInterInc : IsIncreasing (⋂ j ∈ s, A j) := by
        apply isIncreasing_iInter
        intro j
        apply isIncreasing_iInter
        intro _
        exact hA j
      
      have hstep := ih (C := ⋂ j ∈ s, A j) (le_refl _)
      
      have hincl : A i ∩ (⋂ j ∈ s, A j) ⊆ C := by
        refine subset_trans ?_ hsub
        intro ω hω
        rw [Set.mem_iInter₂]
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hjs
        · exact hω.1
        · exact (Set.mem_iInter₂.mp hω.2) j hjs
      calc μ.real (A i) * (∏ j ∈ s, μ.real (A j))
          ≤ μ.real (A i) * μ.real (⋂ j ∈ s, A j) := by
            apply mul_le_mul_of_nonneg_left hstep (measureReal_nonneg)
        _ ≤ μ.real (A i ∩ (⋂ j ∈ s, A j)) := hpa _ _ (hA i) hInterInc
        _ ≤ μ.real C := measureReal_mono hincl

end Strip
end RSW
end StatMech
