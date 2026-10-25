/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsFull.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Def.StatisticalMechanics.Code.Ising.PeierlsUncond.Part7
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


lemma probContour_nonneg (K : Set (Site d)) (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β : ℝ) : 0 ≤ probContour K η n B β := by
  unfold probContour
  refine Finset.sum_nonneg (fun τ _ => ?_)
  split
  · exact fvProb_nonneg η n B β 0 τ
  · exact le_refl 0


theorem contour_energy_bound (n : ℕ) (K : Set (Site d)) (hK : K ⊆ box d n)
    (η : ConfigSpace (Site d)) (B : Finset (Sym2 (Site d))) (β : ℝ) :
    probContour K η n B β ≤ Real.exp (-(2 * β) * (contourLen K B : ℝ)) := by
  classical
  set c : ℝ := Real.exp (-(2 * β) * (contourLen K B : ℝ)) with hc
  have hcpos : 0 < c := Real.exp_pos _
  
  have hnum : (∑ τ : {x // x ∈ box d n} → Bool,
        (if ContourEvent K B (glue η τ) then fvWeight η n B β 0 τ else 0))
      ≤ c * fvZ η n B β 0 := by
    
    have hstep : (∑ τ : {x // x ∈ box d n} → Bool,
          (if ContourEvent K B (glue η τ) then fvWeight η n B β 0 τ else 0))
        = ∑ τ : {x // x ∈ box d n} → Bool,
            (if ContourEvent K B (glue η τ)
              then c * fvWeight η n B β 0 (flipInteriorOn K τ) else 0) := by
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      by_cases hev : ContourEvent K B (glue η τ)
      · rw [if_pos hev, if_pos hev, hc,
          fvWeight_flipInteriorOn_eq_of_event n K hK η B β τ hev]
      · rw [if_neg hev, if_neg hev]
    rw [hstep]
    
    calc (∑ τ : {x // x ∈ box d n} → Bool,
            (if ContourEvent K B (glue η τ)
              then c * fvWeight η n B β 0 (flipInteriorOn K τ) else 0))
        ≤ ∑ τ : {x // x ∈ box d n} → Bool, c * fvWeight η n B β 0 (flipInteriorOn K τ) := by
          refine Finset.sum_le_sum (fun τ _ => ?_)
          split
          · exact le_refl _
          · exact mul_nonneg hcpos.le (fvWeight_nonneg η n B β 0 _)
      _ = c * ∑ τ : {x // x ∈ box d n} → Bool, fvWeight η n B β 0 (flipInteriorOn K τ) := by
          rw [Finset.mul_sum]
      _ = c * ∑ τ : {x // x ∈ box d n} → Bool, fvWeight η n B β 0 τ := by
          congr 1
          exact Equiv.sum_comp (flipInteriorOnEquiv K) (fun τ => fvWeight η n B β 0 τ)
      _ = c * fvZ η n B β 0 := by rw [fvZ]
  
  unfold probContour fvProb
  have hZpos : 0 < fvZ η n B β 0 := fvZ_pos η n B β 0
  have hrw : (∑ τ : {x // x ∈ box d n} → Bool,
        (if ContourEvent K B (glue η τ) then fvWeight η n B β 0 τ / fvZ η n B β 0 else 0))
      = (∑ τ : {x // x ∈ box d n} → Bool,
          (if ContourEvent K B (glue η τ) then fvWeight η n B β 0 τ else 0)) / fvZ η n B β 0 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    by_cases hev : ContourEvent K B (glue η τ)
    · rw [if_pos hev, if_pos hev]
    · rw [if_neg hev, if_neg hev, zero_div]
  rw [hrw, div_le_iff₀ hZpos]
  linarith [hnum]


end Ising
end StatMech
