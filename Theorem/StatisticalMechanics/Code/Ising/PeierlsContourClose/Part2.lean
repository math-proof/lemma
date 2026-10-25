/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsUncond.Part11
import Def.StatisticalMechanics.Code.Ising.PeierlsContourClose
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


lemma pcc_mem_originClusterFamily {n : ℕ} {K : Finset (Site d)} :
    K ∈ originClusterFamily (d := d) n ↔ K ∈ clusterFamily (d := d) n ∧ origin d ∈ K := by
  unfold originClusterFamily; rw [Finset.mem_filter]


lemma pcc_minusClusterFinset_mem_originFamily {n : ℕ} (τ : {x // x ∈ box d n} → Bool)
    (ho : glue (plusField d) τ (origin d) = false) :
    minusClusterFinset τ ho ∈ originClusterFamily (d := d) n := by
  rw [pcc_mem_originClusterFamily]
  refine ⟨minusClusterFinset_mem_family τ ho, ?_⟩
  rw [minusClusterFinset, Set.Finite.mem_toFinset]
  exact origin_mem_minusCluster (origin d)


theorem pcc_probOriginMinus_le_sum_probContour_origin (n : ℕ) (β : ℝ) :
    probOriginMinus (plusField d) n (bondFinsetTouch d n) β 0
      ≤ ∑ K ∈ originClusterFamily (d := d) n,
          probContour (↑K) (plusField d) n (bondFinsetTouch d n) β := by
  classical
  unfold probOriginMinus probContour
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun τ _ => ?_)
  set g : Finset (Site d) → ℝ := fun K =>
    (if ContourEvent (↑K) (bondFinsetTouch d n) (glue (plusField d) τ)
      then fvProb (plusField d) n (bondFinsetTouch d n) β 0 τ else 0) with hg
  have hgnn : ∀ K ∈ originClusterFamily (d := d) n, 0 ≤ g K := by
    intro K _; rw [hg]; dsimp only; split
    · exact fvProb_nonneg _ _ _ _ _ _
    · exact le_refl 0
  by_cases ho : glue (plusField d) τ (origin d) = false
  · rw [if_pos ho]
    have hKmem : minusClusterFinset τ ho ∈ originClusterFamily (d := d) n :=
      pcc_minusClusterFinset_mem_originFamily τ ho
    have hev : ContourEvent (↑(minusClusterFinset τ ho)) (bondFinsetTouch d n)
        (glue (plusField d) τ) := by
      rw [minusClusterFinset_coe τ ho]; exact contourEvent_of_origin_minus n ho
    have hge : fvProb (plusField d) n (bondFinsetTouch d n) β 0 τ
        = g (minusClusterFinset τ ho) := by rw [hg]; dsimp only; rw [if_pos hev]
    rw [hge]
    exact Finset.single_le_sum hgnn hKmem
  · rw [if_neg ho]
    exact Finset.sum_nonneg hgnn

set_option maxHeartbeats 1000000 in


theorem pcc_probOriginMinus_le_sum_origin (n : ℕ) (β : ℝ) :
    probOriginMinus (plusField d) n (bondFinsetTouch d n) β 0
      ≤ ∑ K ∈ originClusterFamily (d := d) n,
          Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch d n) : ℝ)) := by
  refine le_trans (pcc_probOriginMinus_le_sum_probContour_origin n β) ?_
  apply Finset.sum_le_sum
  intro K hK
  have hKfam : K ∈ clusterFamily (d := d) n := (pcc_mem_originClusterFamily.mp hK).1
  have hKbox : (↑K : Set (Site d)) ⊆ box d n := clusterFamily_subset_box hKfam
  have hbound := contour_energy_bound n (↑K) hKbox (plusField d) (bondFinsetTouch d n) β
  exact hbound


end Ising
end StatMech
