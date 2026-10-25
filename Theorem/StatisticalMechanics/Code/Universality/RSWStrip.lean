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
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip


theorem PositivelyAssociated.decreasing {E : Type*} (μ : Measure (ConfigSpace E))
    [IsProbabilityMeasure μ] (hpa : PositivelyAssociated μ)
    {A B : Set (ConfigSpace E)} (hA : IsDecreasing A) (hB : IsDecreasing B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    μ.real A * μ.real B ≤ μ.real (A ∩ B) := by
  
  have hfkg := hpa Aᶜ Bᶜ hA.compl hB.compl
  have hca : μ.real Aᶜ = 1 - μ.real A := by rw [measureReal_compl hAm, probReal_univ]
  have hcb : μ.real Bᶜ = 1 - μ.real B := by rw [measureReal_compl hBm, probReal_univ]
  have hcum : μ.real (Aᶜ ∩ Bᶜ) = 1 - μ.real (A ∪ B) := by
    rw [← Set.compl_union, measureReal_compl (hAm.union hBm), probReal_univ]
  rw [hca, hcb, hcum] at hfkg
  
  have hie : μ.real (A ∪ B) + μ.real (A ∩ B) = μ.real A + μ.real B :=
    measureReal_union_add_inter hBm
  nlinarith [hfkg, hie]


theorem complUnion_fkg_bound {E : Type*} (μ : Measure (ConfigSpace E))
    [IsProbabilityMeasure μ] (hpa : PositivelyAssociated μ)
    {A B : Set (ConfigSpace E)} (hA : IsIncreasing A) (hB : IsIncreasing B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (1 - μ.real A) * (1 - μ.real B) ≤ 1 - μ.real (A ∪ B) := by
  have hdec := hpa.decreasing μ hA.compl hB.compl hAm.compl hBm.compl
  have hca : μ.real Aᶜ = 1 - μ.real A := by rw [measureReal_compl hAm, probReal_univ]
  have hcb : μ.real Bᶜ = 1 - μ.real B := by rw [measureReal_compl hBm, probReal_univ]
  have hcum : μ.real (Aᶜ ∩ Bᶜ) = 1 - μ.real (A ∪ B) := by
    rw [← Set.compl_union, measureReal_compl (hAm.union hBm), probReal_univ]
  rw [hca, hcb, hcum] at hdec
  exact hdec


theorem sqrt_trick_max_real {a b s : ℝ} (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (h : (1 - a) * (1 - b) ≤ 1 - s) :
    1 - Real.sqrt (1 - s) ≤ max a b := by
  rcases le_total a b with hab | hba
  · 
    have h1b : (0 : ℝ) ≤ 1 - b := by linarith
    have hbb : (1 - b) ^ 2 ≤ 1 - s := by nlinarith
    have hsq : Real.sqrt ((1 - b) ^ 2) ≤ Real.sqrt (1 - s) := Real.sqrt_le_sqrt hbb
    rw [Real.sqrt_sq h1b] at hsq
    rw [max_eq_right hab]; linarith
  · have h1a : (0 : ℝ) ≤ 1 - a := by linarith
    have haa : (1 - a) ^ 2 ≤ 1 - s := by nlinarith
    have hsq : Real.sqrt ((1 - a) ^ 2) ≤ Real.sqrt (1 - s) := Real.sqrt_le_sqrt haa
    rw [Real.sqrt_sq h1a] at hsq
    rw [max_eq_left hba]; linarith


theorem rsw_sqrt_trick {E : Type*} (μ : Measure (ConfigSpace E))
    [IsProbabilityMeasure μ] (hpa : PositivelyAssociated μ)
    {A B : Set (ConfigSpace E)} (hA : IsIncreasing A) (hB : IsIncreasing B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    1 - Real.sqrt (1 - μ.real (A ∪ B)) ≤ max (μ.real A) (μ.real B) :=
  sqrt_trick_max_real measureReal_le_one measureReal_le_one
    (complUnion_fkg_bound μ hpa hA hB hAm hBm)


theorem rsw_sqrt_trick_eq {E : Type*} (μ : Measure (ConfigSpace E))
    [IsProbabilityMeasure μ] (hpa : PositivelyAssociated μ)
    {A B : Set (ConfigSpace E)} (hA : IsIncreasing A) (hB : IsIncreasing B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hAB : μ.real A = μ.real B) :
    1 - Real.sqrt (1 - μ.real (A ∪ B)) ≤ μ.real A := by
  have := rsw_sqrt_trick μ hpa hA hB hAm hBm
  rwa [← hAB, max_self] at this


theorem hv_glue {ω : ConfigSpace (Sym2 (Site 2))} {a m m' b c d : ℤ}
    (ham : a ≤ m) (hm'b : m' ≤ b)
    {xL : Site 2} (hxL : xL ∈ leftSide a m' c d)
    {p : Site 2} (hpO : p ∈ rect m m' c d) (hpL : p ∈ rect a m' c d)
    (hc1 : ConnectedWithin 2 ω (rect a m' c d) ⟨xL, leftSide_subset hxL⟩ ⟨p, hpL⟩)
    {q : Site 2} (hqO : q ∈ rect m m' c d)
    (hcV : ConnectedWithin 2 ω (rect m m' c d) ⟨p, hpO⟩ ⟨q, hqO⟩)
    {yR : Site 2} (hyR : yR ∈ rightSide m b c d) (hqR : q ∈ rect m b c d)
    (hc2 : ConnectedWithin 2 ω (rect m b c d) ⟨q, hqR⟩ ⟨yR, rightSide_subset hyR⟩) :
    HorizontalCrossing ω a b c d := by
  
  have hsubL : rect a m' c d ⊆ rect a b c d := rect_subset_of_right hm'b
  have hsubO : rect m m' c d ⊆ rect a b c d := fun x hx =>
    ⟨le_trans ham hx.1, le_trans hx.2.1 hm'b, hx.2.2.1, hx.2.2.2⟩
  have hsubR : rect m b c d ⊆ rect a b c d := rect_subset_of_left ham
  have hxLab : xL ∈ leftSide a b c d := ⟨hsubL (leftSide_subset hxL), hxL.2⟩
  have hyRab : yR ∈ rightSide a b c d := ⟨hsubR (rightSide_subset hyR), hyR.2⟩
  refine ⟨⟨xL, hxLab⟩, ⟨yR, hyRab⟩, ?_⟩
  
  have e1 := connectedWithin_mono_set ω hsubL hc1
  have eV := connectedWithin_mono_set ω hsubO hcV
  have e2 := connectedWithin_mono_set ω hsubR hc2
  exact (e1.trans eV).trans e2


end Universality
end StatMech
