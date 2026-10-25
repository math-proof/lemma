/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsOuterContour.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Def.StatisticalMechanics.Code.Ising.PeierlsOuterClose
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Percolation (anchorFinset)

attribute [local instance] Classical.propDecidable


theorem mem_holeFreeClusterFamily {n : ℕ} {K : Finset (Site 2)} :
    K ∈ holeFreeClusterFamily n ↔
      K ∈ clusterFamily (d := 2) n ∧ IsHoleFreeBoxCluster n K := by
  unfold holeFreeClusterFamily; rw [Finset.mem_filter]


theorem holeFreeClusterFamily_subset_box {n : ℕ} {K : Finset (Site 2)}
    (hK : K ∈ holeFreeClusterFamily n) : (↑K : Set (Site 2)) ⊆ box 2 n :=
  clusterFamily_subset_box (mem_holeFreeClusterFamily.mp hK).1


theorem outerUnionBound_le_sum_probContour (n : ℕ) (β : ℝ) (hWind : OuterContourWinding n) :
    probOriginMinus (plusField 2) n (bondFinsetTouch 2 n) β 0
      ≤ ∑ K ∈ holeFreeClusterFamily n,
          probContour (↑K) (plusField 2) n (bondFinsetTouch 2 n) β := by
  classical
  unfold probOriginMinus probContour
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun τ _ => ?_)
  set g : Finset (Site 2) → ℝ := fun K =>
    (if ContourEvent (↑K) (bondFinsetTouch 2 n) (glue (plusField 2) τ)
      then fvProb (plusField 2) n (bondFinsetTouch 2 n) β 0 τ else 0) with hg
  have hgnn : ∀ K ∈ holeFreeClusterFamily n, 0 ≤ g K := by
    intro K _; rw [hg]; dsimp only; split
    · exact fvProb_nonneg _ _ _ _ _ _
    · exact le_refl 0
  by_cases ho : glue (plusField 2) τ (origin 2) = false
  · rw [if_pos ho]
    obtain ⟨K, hKbox, hKconn, hev, T, j, hsupp, hj, hax, hcov⟩ := hWind τ ho
    
    have hKbox' : K ⊆ boxFinset 2 n := by
      intro x hx; rw [mem_boxFinset]; exact hKbox (Finset.mem_coe.mpr hx)
    have hKfam : K ∈ clusterFamily (d := 2) n := by
      rw [clusterFamily, Finset.mem_powerset]; exact hKbox'
    have hKmem : K ∈ holeFreeClusterFamily n := by
      rw [mem_holeFreeClusterFamily]
      exact ⟨hKfam, hKconn, T, j, hsupp, hj, hax, hcov⟩
    have hge : fvProb (plusField 2) n (bondFinsetTouch 2 n) β 0 τ
        = g K := by rw [hg]; dsimp only; rw [if_pos hev]
    rw [hge]
    exact Finset.single_le_sum hgnn hKmem
  · rw [if_neg ho]
    exact Finset.sum_nonneg hgnn

set_option maxHeartbeats 1000000 in


theorem outerUnionBound_le_sum_exp (n : ℕ) (β : ℝ) (hWind : OuterContourWinding n) :
    probOriginMinus (plusField 2) n (bondFinsetTouch 2 n) β 0
      ≤ ∑ K ∈ holeFreeClusterFamily n,
          Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch 2 n) : ℝ)) := by
  refine le_trans (outerUnionBound_le_sum_probContour n β hWind) ?_
  apply Finset.sum_le_sum
  intro K hK
  have hKbox := holeFreeClusterFamily_subset_box hK
  have hbound := contour_energy_bound n (↑K) hKbox (plusField 2) (bondFinsetTouch 2 n) β
  exact hbound


end Ising
end StatMech
