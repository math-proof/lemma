/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsContourCount.Part4
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


theorem pcl_contourEnergy_eq_pow (β : ℝ) (ℓ : ℕ) :
    Real.exp (-(2 * β) * (ℓ : ℝ)) = (Real.exp (-(2 * β))) ^ ℓ := by
  rw [← Real.exp_nat_mul, mul_comm]


theorem pcl_summand_eq (d : ℕ) (β : ℝ) (ℓ : ℕ) :
    (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * (Real.exp (-(2 * β))) ^ ℓ
      = (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ)) := by
  rw [pcl_contourEnergy_eq_pow]


theorem pcl_summable_peierlsSummand (d : ℕ) (β : ℝ) (hx : peierlsRatio d β < 1) :
    Summable (fun ℓ : ℕ => (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ))) := by
  have heq : (fun ℓ : ℕ => (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ)))
      = (fun ℓ : ℕ => (ℓ : ℝ) * (peierlsRatio d β) ^ ℓ) :=
    funext (peierlsSummand_eq d β)
  rw [heq]
  have hnorm : ‖peierlsRatio d β‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (peierlsRatio_nonneg d β)]; exact hx
  have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
  simpa using this


theorem pcl_lengthSum_le_peierlsBound (d : ℕ) (β : ℝ) (hx : peierlsRatio d β < 1)
    (T : Finset ℕ) :
    ∑ ℓ ∈ T, (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ)) ≤ peierlsBound d β :=
  Summable.sum_le_tsum T (fun ℓ _ => by positivity) (pcl_summable_peierlsSummand d β hx)


theorem pcl_clusterSum_le_lengthSum {α : Type*} [DecidableEq α] (S : Finset α) (len : α → ℕ)
    (c : ℝ) (hc : 0 ≤ c) (count : ℕ → ℝ)
    (hcount : ∀ ℓ, ((S.filter (fun K => len K = ℓ)).card : ℝ) ≤ count ℓ) :
    ∑ K ∈ S, c ^ (len K) ≤ ∑ ℓ ∈ S.image len, count ℓ * c ^ ℓ := by
  have hmaps : ∀ K ∈ S, len K ∈ S.image len := fun K hK => Finset.mem_image_of_mem len hK
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun K => c ^ (len K))]
  refine Finset.sum_le_sum (fun ℓ _ => ?_)
  have hinner : ∑ K ∈ S.filter (fun K => len K = ℓ), c ^ (len K)
      = ((S.filter (fun K => len K = ℓ)).card : ℝ) * c ^ ℓ := by
    rw [Finset.sum_congr rfl (fun K hK => by rw [(Finset.mem_filter.mp hK).2])]
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hinner]
  exact mul_le_mul_of_nonneg_right (hcount ℓ) (by positivity)


end Ising
end StatMech
