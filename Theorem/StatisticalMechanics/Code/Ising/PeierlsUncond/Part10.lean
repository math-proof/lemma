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
import Def.StatisticalMechanics.Code.Ising.PeierlsUncond.Part10
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


lemma minusClusterFinset_mem_family {n : ℕ} (τ : {x // x ∈ box d n} → Bool)
    (ho : glue (plusField d) τ (origin d) = false) :
    minusClusterFinset τ ho ∈ clusterFamily (d := d) n := by
  unfold clusterFamily minusClusterFinset
  rw [Finset.mem_powerset]
  intro x hx
  rw [Set.Finite.mem_toFinset] at hx
  rw [mem_boxFinset]
  exact minusCluster_glue_plus_subset_box τ ho hx

lemma minusClusterFinset_coe {n : ℕ} (τ : {x // x ∈ box d n} → Bool)
    (ho : glue (plusField d) τ (origin d) = false) :
    ((minusClusterFinset τ ho : Finset (Site d)) : Set (Site d))
      = minusCluster (glue (plusField d) τ) (origin d) :=
  Set.Finite.coe_toFinset _

set_option maxHeartbeats 1000000 in
lemma clusterFamily_subset_boxFinset {n : ℕ} {K : Finset (Site d)}
    (hK : K ∈ clusterFamily (d := d) n) : K ⊆ boxFinset d n :=
  Finset.mem_powerset.mp hK

lemma clusterFamily_subset_box {n : ℕ} {K : Finset (Site d)}
    (hK : K ∈ clusterFamily (d := d) n) : (↑K : Set (Site d)) ⊆ box d n := by
  intro x hx
  rw [Finset.mem_coe] at hx
  have hmem := clusterFamily_subset_boxFinset hK hx
  rw [mem_boxFinset] at hmem
  exact hmem


theorem probOriginMinus_le_sum_probContour (n : ℕ) (β : ℝ) :
    probOriginMinus (plusField d) n (bondFinsetTouch d n) β 0
      ≤ ∑ K ∈ clusterFamily (d := d) n,
          probContour (↑K) (plusField d) n (bondFinsetTouch d n) β := by
  classical
  unfold probOriginMinus probContour
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun τ _ => ?_)
  set g : Finset (Site d) → ℝ := fun K =>
    (if ContourEvent (↑K) (bondFinsetTouch d n) (glue (plusField d) τ)
      then fvProb (plusField d) n (bondFinsetTouch d n) β 0 τ else 0) with hg
  have hgnn : ∀ K ∈ clusterFamily (d := d) n, 0 ≤ g K := by
    intro K _; rw [hg]; dsimp only; split
    · exact fvProb_nonneg _ _ _ _ _ _
    · exact le_refl 0
  by_cases ho : glue (plusField d) τ (origin d) = false
  · rw [if_pos ho]
    have hKmem : minusClusterFinset τ ho ∈ clusterFamily (d := d) n :=
      minusClusterFinset_mem_family τ ho
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


theorem probOriginMinus_le_sum_exp (n : ℕ) (β : ℝ) :
    probOriginMinus (plusField d) n (bondFinsetTouch d n) β 0
      ≤ ∑ K ∈ clusterFamily (d := d) n,
          Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch d n) : ℝ)) := by
  refine le_trans (probOriginMinus_le_sum_probContour n β) ?_
  apply Finset.sum_le_sum
  intro K hK
  have hKbox : (↑K : Set (Site d)) ⊆ box d n := clusterFamily_subset_box hK
  have hbound := contour_energy_bound n (↑K) hKbox (plusField d) (bondFinsetTouch d n) β
  exact hbound


end Ising
end StatMech
