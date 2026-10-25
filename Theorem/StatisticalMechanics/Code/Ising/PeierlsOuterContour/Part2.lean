/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterContour.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsClose.Part2
import Theorem.StatisticalMechanics.Code.Ising.PeierlsContourCount.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
import Def.StatisticalMechanics.Code.Ising.PeierlsOuterContour
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Percolation (anchorFinset)

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


theorem poc_twoPeierlsBound_nonneg (d : ℕ) (β : ℝ) : 0 ≤ twoPeierlsBound d β := by
  unfold twoPeierlsBound; have := peierlsBound_nonneg d β; linarith


theorem poc_twoPeierlsBound_tendsto_atTop (d : ℕ) :
    Tendsto (fun β : ℝ => twoPeierlsBound d β) atTop (nhds 0) := by
  have h := (peierlsBound_tendsto_atTop d).const_mul (2 : ℝ)
  simpa [twoPeierlsBound] using h


theorem poc_exists_beta_two_peierlsBound_lt_half (d : ℕ) :
    ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β → twoPeierlsBound d β < 1 / 2 := by
  have h := (poc_twoPeierlsBound_tendsto_atTop d).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  rw [eventually_atTop] at h
  obtain ⟨β₀, hβ₀⟩ := h
  exact ⟨β₀, hβ₀⟩


theorem poc_circuitLengthSum_le (β : ℝ) (hx : peierlsRatio 2 β < 1) (T : Finset ℕ) :
    ∑ ℓ ∈ T, ((Percolation.cyclesAtLen ℓ).card : ℝ) * Real.exp (-(2 * β) * (ℓ : ℝ))
      ≤ twoPeierlsBound 2 β := by
  have hsummand : Summable
      (fun ℓ : ℕ => (ℓ : ℝ) * (2 * 2 : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ))) :=
    pcl_summable_peierlsSummand 2 β hx
  
  have hterm : ∀ ℓ ∈ T,
      ((Percolation.cyclesAtLen ℓ).card : ℝ) * Real.exp (-(2 * β) * (ℓ : ℝ))
        ≤ 2 * ((ℓ : ℝ) * (2 * 2 : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ))) := by
    intro ℓ _
    have hexp : (0 : ℝ) ≤ Real.exp (-(2 * β) * (ℓ : ℝ)) := (Real.exp_pos _).le
    calc ((Percolation.cyclesAtLen ℓ).card : ℝ) * Real.exp (-(2 * β) * (ℓ : ℝ))
        ≤ (2 * ((ℓ : ℝ) * (2 * 2 : ℝ) ^ ℓ)) * Real.exp (-(2 * β) * (ℓ : ℝ)) :=
          mul_le_mul_of_nonneg_right (poc_cyclesAtLen_card_le_real ℓ) hexp
      _ = 2 * ((ℓ : ℝ) * (2 * 2 : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ))) := by ring
  calc ∑ ℓ ∈ T, ((Percolation.cyclesAtLen ℓ).card : ℝ) * Real.exp (-(2 * β) * (ℓ : ℝ))
      ≤ ∑ ℓ ∈ T, 2 * ((ℓ : ℝ) * (2 * 2 : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ))) :=
        Finset.sum_le_sum hterm
    _ = 2 * ∑ ℓ ∈ T, ((ℓ : ℝ) * (2 * 2 : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ))) := by
        rw [Finset.mul_sum]
    _ ≤ 2 * peierlsBound 2 β := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact pcl_lengthSum_le_peierlsBound 2 β hx T
    _ = twoPeierlsBound 2 β := rfl


theorem poc_probContourCircuit_le (n : ℕ) (K : Set (Site d)) (hK : K ⊆ box d n)
    (η : ConfigSpace (Site d)) (β : ℝ) :
    probContour K η n (bondFinsetTouch d n) β
      ≤ Real.exp (-(2 * β) * (contourLen K (bondFinsetTouch d n) : ℝ)) :=
  contour_energy_bound n K hK η (bondFinsetTouch d n) β


end Ising
end StatMech
