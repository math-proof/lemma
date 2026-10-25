/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCrossBoxCap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtreme
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusErgodicClose
import Theorem.StatisticalMechanics.Code.FK.FKMixingUpperClose.Part5
import Theorem.StatisticalMechanics.Code.FK.ErgodicExtremeUpgrade
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.FK

open StatMech.Percolation

variable {d : ℕ}


theorem icb_plus_box_monotone {N m : ℕ} (hNm : N ≤ m) (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    {A : Set (ConfigSpace (Site d))} (hA : MeasurableSet A) (hAinc : IsIncreasing A) :
    (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real A
      ≤ (plusMeasure d N β h : Measure (ConfigSpace (Site d))).real A := by
  set g0 : ConfigSpace (Site d) → ℝ := A.indicator (fun _ => (1:ℝ)) with hg0
  have hcds := consistency_double_sum hNm (plusField d) β h g0
  have hpm_m : (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real A
      = ∑ σ : {x // x ∈ box d m} → Bool,
          fvProb (plusField d) m (bondFinsetTouch d m) β h σ * g0 (glue (plusField d) σ) := by
    rw [plusMeasure_coe, fvMeasure_real_eq (plusField d) m (bondFinsetTouch d m) β h hA]
  rw [hpm_m, ← hcds]
  have hterm : ∀ σ : {x // x ∈ box d m} → Bool,
      fvProb (plusField d) m (bondFinsetTouch d m) β h σ
        * ∑ τ : {x // x ∈ box d N} → Bool,
            fvProb (glue (plusField d) σ) N (bondFinsetTouch d N) β h τ
              * g0 (glue (glue (plusField d) σ) τ)
      ≤ fvProb (plusField d) m (bondFinsetTouch d m) β h σ
          * (plusMeasure d N β h : Measure (ConfigSpace (Site d))).real A := by
    intro σ
    apply mul_le_mul_of_nonneg_left _ (fvProb_nonneg _ _ _ _ _ _)
    have hinner : (∑ τ : {x // x ∈ box d N} → Bool,
            fvProb (glue (plusField d) σ) N (bondFinsetTouch d N) β h τ
              * g0 (glue (glue (plusField d) σ) τ))
        = (fvMeasure (glue (plusField d) σ) N (bondFinsetTouch d N) β h).real A := by
      rw [fvMeasure_real_eq (glue (plusField d) σ) N (bondFinsetTouch d N) β h hA]
    rw [hinner]
    have hdom := fvMeasure_le_plusField N (bondFinsetTouch d N) β h hβ hh (glue (plusField d) σ)
      A hA hAinc
    refine hdom.trans (le_of_eq ?_)
    rw [plusMeasure_coe]
  calc (∑ σ : {x // x ∈ box d m} → Bool,
          fvProb (plusField d) m (bondFinsetTouch d m) β h σ
            * ∑ τ : {x // x ∈ box d N} → Bool,
                fvProb (glue (plusField d) σ) N (bondFinsetTouch d N) β h τ
                  * g0 (glue (glue (plusField d) σ) τ))
      ≤ ∑ σ : {x // x ∈ box d m} → Bool,
          fvProb (plusField d) m (bondFinsetTouch d m) β h σ
            * (plusMeasure d N β h : Measure (ConfigSpace (Site d))).real A :=
        Finset.sum_le_sum (fun σ _ => hterm σ)
    _ = (plusMeasure d N β h : Measure (ConfigSpace (Site d))).real A := by
        rw [← Finset.sum_mul, fvProb_sum_eq_one, one_mul]


theorem icb_multiOpen_glue_ovrBox_eq {N m : ℕ} (hNm : N ≤ m) (S : Finset (Site d))
    (hS : ∀ x ∈ S, x ∉ box d N)
    (σ : {x // x ∈ box d m} → Bool) (τ : {x // x ∈ box d N} → Bool) :
    (fmu_multiOpen S).indicator (fun _ => (1:ℝ)) (glue (plusField d) (ovrBox hNm σ τ))
      = (fmu_multiOpen S).indicator (fun _ => (1:ℝ)) (glue (plusField d) σ) := by
  have heq : ∀ x ∈ S, glue (plusField d) (ovrBox hNm σ τ) x = glue (plusField d) σ x :=
    fun x hx => glue_ovrBox_eq_off_box hNm (plusField d) σ τ (hS x hx)
  by_cases hmem : glue (plusField d) (ovrBox hNm σ τ) ∈ fmu_multiOpen S
  · have hmem' : glue (plusField d) σ ∈ fmu_multiOpen S := by
      intro x hx; rw [← heq x hx]; exact hmem x hx
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem']
  · have hmem' : glue (plusField d) σ ∉ fmu_multiOpen S := by
      intro hc; apply hmem; intro x hx; rw [heq x hx]; exact hc x hx
    rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem']


theorem icb_box_cross_cap {N m : ℕ} (hNm : N ≤ m) (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    {A : Set (ConfigSpace (Site d))} (hA : MeasurableSet A) (hAinc : IsIncreasing A)
    (S : Finset (Site d)) (hS : ∀ x ∈ S, x ∉ box d N) :
    (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real (A ∩ fmu_multiOpen S)
      ≤ (plusMeasure d N β h : Measure (ConfigSpace (Site d))).real A
        * (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen S) := by
  classical
  have hBmeas : MeasurableSet (fmu_multiOpen S) := fmu_multiOpen_measurable S
  have hcapmeas : MeasurableSet (A ∩ fmu_multiOpen S) := hA.inter hBmeas
  set g0 : ConfigSpace (Site d) → ℝ := (A ∩ fmu_multiOpen S).indicator (fun _ => (1:ℝ)) with hg0
  have hcds := consistency_double_sum hNm (plusField d) β h g0
  have hpm_cap : (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real (A ∩ fmu_multiOpen S)
      = ∑ σ : {x // x ∈ box d m} → Bool,
          fvProb (plusField d) m (bondFinsetTouch d m) β h σ * g0 (glue (plusField d) σ) := by
    rw [plusMeasure_coe, fvMeasure_real_eq (plusField d) m (bondFinsetTouch d m) β h hcapmeas]
  rw [hpm_cap, ← hcds]
  have hterm : ∀ σ : {x // x ∈ box d m} → Bool,
      fvProb (plusField d) m (bondFinsetTouch d m) β h σ
        * ∑ τ : {x // x ∈ box d N} → Bool,
            fvProb (glue (plusField d) σ) N (bondFinsetTouch d N) β h τ
              * g0 (glue (glue (plusField d) σ) τ)
      ≤ fvProb (plusField d) m (bondFinsetTouch d m) β h σ
          * ((plusMeasure d N β h : Measure (ConfigSpace (Site d))).real A
              * (fmu_multiOpen S).indicator (fun _ => (1:ℝ)) (glue (plusField d) σ)) := by
    intro σ
    apply mul_le_mul_of_nonneg_left _ (fvProb_nonneg _ _ _ _ _ _)
    have hsplit : ∀ τ : {x // x ∈ box d N} → Bool,
        fvProb (glue (plusField d) σ) N (bondFinsetTouch d N) β h τ
            * g0 (glue (glue (plusField d) σ) τ)
        = ((fmu_multiOpen S).indicator (fun _ => (1:ℝ)) (glue (plusField d) σ))
            * (fvProb (glue (plusField d) σ) N (bondFinsetTouch d N) β h τ
              * A.indicator (fun _ => (1:ℝ)) (glue (glue (plusField d) σ) τ)) := by
      intro τ
      have hind : ∀ y : ConfigSpace (Site d),
          g0 y = A.indicator (fun _ => (1:ℝ)) y * (fmu_multiOpen S).indicator (fun _ => (1:ℝ)) y := by
        intro y; rw [hg0]
        have := Set.inter_indicator_mul (s := A) (t := fmu_multiOpen S)
          (fun _ => (1:ℝ)) (fun _ => (1:ℝ)) y
        simpa using this
      rw [hind, glue_glue_eq_glue_ovrBox hNm (plusField d) σ τ,
        icb_multiOpen_glue_ovrBox_eq hNm S hS σ τ,
        ← glue_glue_eq_glue_ovrBox hNm (plusField d) σ τ]
      ring
    rw [Finset.sum_congr rfl (fun τ _ => hsplit τ), ← Finset.mul_sum]
    rw [mul_comm ((plusMeasure d N β h : Measure (ConfigSpace (Site d))).real A) _]
    apply mul_le_mul_of_nonneg_left _ (Set.indicator_nonneg (fun _ _ => by norm_num) _)
    have hinner : (∑ τ : {x // x ∈ box d N} → Bool,
            fvProb (glue (plusField d) σ) N (bondFinsetTouch d N) β h τ
              * A.indicator (fun _ => (1:ℝ)) (glue (glue (plusField d) σ) τ))
        = (fvMeasure (glue (plusField d) σ) N (bondFinsetTouch d N) β h).real A := by
      rw [fvMeasure_real_eq (glue (plusField d) σ) N (bondFinsetTouch d N) β h hA]
    rw [hinner]
    have hdom := fvMeasure_le_plusField N (bondFinsetTouch d N) β h hβ hh (glue (plusField d) σ)
      A hA hAinc
    refine hdom.trans (le_of_eq ?_); rw [plusMeasure_coe]
  calc (∑ σ : {x // x ∈ box d m} → Bool,
          fvProb (plusField d) m (bondFinsetTouch d m) β h σ
            * ∑ τ : {x // x ∈ box d N} → Bool,
                fvProb (glue (plusField d) σ) N (bondFinsetTouch d N) β h τ
                  * g0 (glue (glue (plusField d) σ) τ))
      ≤ ∑ σ : {x // x ∈ box d m} → Bool,
          fvProb (plusField d) m (bondFinsetTouch d m) β h σ
            * ((plusMeasure d N β h : Measure (ConfigSpace (Site d))).real A
                * (fmu_multiOpen S).indicator (fun _ => (1:ℝ)) (glue (plusField d) σ)) :=
        Finset.sum_le_sum (fun σ _ => hterm σ)
    _ = (plusMeasure d N β h : Measure (ConfigSpace (Site d))).real A
          * (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen S) := by
        rw [show (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen S)
              = ∑ σ : {x // x ∈ box d m} → Bool,
                  fvProb (plusField d) m (bondFinsetTouch d m) β h σ
                    * (fmu_multiOpen S).indicator (fun _ => (1:ℝ)) (glue (plusField d) σ) from by
            rw [plusMeasure_coe, fvMeasure_real_eq (plusField d) m (bondFinsetTouch d m) β h hBmeas]]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro σ _; ring


end Ising
end StatMech
