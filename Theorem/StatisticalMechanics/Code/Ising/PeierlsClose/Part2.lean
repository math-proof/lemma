/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsContourCount.Part4
import Def.StatisticalMechanics.Code.Ising.PeierlsClose
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


theorem pcl_connectedContourCountBound_of_count (n : ℕ) (β : ℝ)
    (hx : peierlsRatio d β < 1) (hCount : ConnectedContourCount d n) :
    ConnectedContourCountBound d n β := by
  classical
  unfold ConnectedContourCountBound
  
  let S : Finset (Finset (Site d)) := connClusterFamily (d := d) n
  let len : Finset (Site d) → ℕ := fun K => contourLen (↑K) (bondFinsetTouch d n)
  let c : ℝ := Real.exp (-(2 * β))
  show ∑ K ∈ S, Real.exp (-(2 * β) * (len K : ℝ)) ≤ peierlsBound d β
  
  have hrw : ∀ K ∈ S, Real.exp (-(2 * β) * (len K : ℝ)) = c ^ (len K) := fun K _ => by
    change Real.exp (-(2 * β) * (len K : ℝ)) = Real.exp (-(2 * β)) ^ (len K)
    rw [pcl_contourEnergy_eq_pow]
  rw [Finset.sum_congr rfl hrw]
  
  have hgroup := pcl_clusterSum_le_lengthSum (α := Finset (Site d)) S len c (Real.exp_pos _).le
    (fun ℓ => (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ) (fun ℓ => hCount ℓ)
  refine le_trans hgroup ?_
  
  have hpeierls : ∑ ℓ ∈ S.image len, (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * c ^ ℓ
      = ∑ ℓ ∈ S.image len, (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ)) :=
    Finset.sum_congr rfl (fun ℓ _ => by
      change (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β)) ^ ℓ
        = (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ))
      rw [pcl_summand_eq])
  rw [hpeierls]
  exact pcl_lengthSum_le_peierlsBound d β hx (S.image len)


theorem pcl_exists_beta_ratio_lt_one (d : ℕ) :
    ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β → peierlsRatio d β < 1 := by
  have h := (peierlsRatio_tendsto_atTop d).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  rw [eventually_atTop] at h
  obtain ⟨β₀, hβ₀⟩ := h
  exact ⟨β₀, hβ₀⟩


theorem pcl_peierls_long_range_order_of_count (hd : 2 ≤ d)
    (hCount : ∀ n : ℕ, ConnectedContourCount d n) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      plusMeasure d n β 0 ≠ minusMeasure d n β 0 := by
  obtain ⟨β₀, hβ₀⟩ := pcl_exists_beta_ratio_lt_one d
  refine pcc_peierls_long_range_order_of_connected hd ⟨β₀, fun n β hβ => ?_⟩
  exact pcl_connectedContourCountBound_of_count n β (hβ₀ β hβ) (hCount n)

end Ising
end StatMech
