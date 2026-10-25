/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PlusStateTIClose.Part6
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusErgodicClose
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

open StatMech.FK

variable {d : ℕ}


theorem iti_glue_plusField_le {n : ℕ} (σ : {x // x ∈ box d n} → Bool) :
    glue (plusField d) σ ≤ plusField d := by
  intro x; simp only [plusField]; cases (glue (plusField d) σ x) <;> simp

set_option maxHeartbeats 1600000 in


theorem iti_crossbox_dom (n m : ℕ) (hnm : n ≤ m) {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h)
    {A : Set (ConfigSpace (Site d))} (hAmeas : MeasurableSet A) (hAinc : IsIncreasing A) :
    (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real A
      ≤ (plusMeasure d n β h : Measure (ConfigSpace (Site d))).real A := by
  have hLHSm : (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real A
      = ∑ σ : {x // x ∈ box d m} → Bool,
          fvProb (plusField d) m (bondFinsetTouch d m) β h σ
            * Set.indicator A (fun _ => (1:ℝ)) (glue (plusField d) σ) := by
    rw [plusMeasure_coe]; exact fvMeasure_real_eq (plusField d) m (bondFinsetTouch d m) β h hAmeas
  have hcons := consistency_double_sum hnm (plusField d) β h (Set.indicator A (fun _ => (1:ℝ)))
  rw [hLHSm, ← hcons]
  
  have hbound : ∀ σ : {x // x ∈ box d m} → Bool,
      (∑ τ : {x // x ∈ box d n} → Bool,
          fvProb (glue (plusField d) σ) n (bondFinsetTouch d n) β h τ
            * Set.indicator A (fun _ => (1:ℝ)) (glue (glue (plusField d) σ) τ))
        ≤ (plusMeasure d n β h : Measure (ConfigSpace (Site d))).real A := by
    intro σ
    have hd1 : (∑ τ : {x // x ∈ box d n} → Bool,
          fvProb (glue (plusField d) σ) n (bondFinsetTouch d n) β h τ
            * Set.indicator A (fun _ => (1:ℝ)) (glue (glue (plusField d) σ) τ))
        = (fvMeasure (glue (plusField d) σ) n (bondFinsetTouch d n) β h).real A :=
      (fvMeasure_real_eq (glue (plusField d) σ) n (bondFinsetTouch d n) β h hAmeas).symm
    have hdom : (fvMeasure (glue (plusField d) σ) n (bondFinsetTouch d n) β h).real A
        ≤ (fvMeasure (plusField d) n (bondFinsetTouch d n) β h).real A :=
      fvMeasure_dominated n (bondFinsetTouch d n) β h hβ hh
        (glue (plusField d) σ) (plusField d) (iti_glue_plusField_le σ) A hAmeas hAinc
    rw [hd1, plusMeasure_coe]; exact hdom
  calc ∑ σ : {x // x ∈ box d m} → Bool,
          fvProb (plusField d) m (bondFinsetTouch d m) β h σ
            * (∑ τ : {x // x ∈ box d n} → Bool,
                fvProb (glue (plusField d) σ) n (bondFinsetTouch d n) β h τ
                  * Set.indicator A (fun _ => (1:ℝ)) (glue (glue (plusField d) σ) τ))
      ≤ ∑ σ : {x // x ∈ box d m} → Bool,
          fvProb (plusField d) m (bondFinsetTouch d m) β h σ
            * ((plusMeasure d n β h : Measure (ConfigSpace (Site d))).real A) := by
        apply Finset.sum_le_sum
        intro σ _
        exact mul_le_mul_of_nonneg_left (hbound σ) (fvProb_nonneg _ _ _ _ _ _)
    _ = (plusMeasure d n β h : Measure (ConfigSpace (Site d))).real A := by
        rw [← Finset.sum_mul,
          fvProb_sum_eq_one (plusField d) m (bondFinsetTouch d m) β h, one_mul]


theorem iti_plus_multiOpen_antitone {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h)
    (T : Finset (Site d)) {n m : ℕ} (hnm : n ≤ m) :
    (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen (E := Site d) T)
      ≤ (plusMeasure d n β h : Measure (ConfigSpace (Site d))).real
          (fmu_multiOpen (E := Site d) T) :=
  iti_crossbox_dom n m hnm hβ hh
    (IsClopen.measurableSet_configSpace (ipe_multiOpen_isClopen T))
    (fmu_multiOpen_isIncreasing T)


end Ising
end StatMech
