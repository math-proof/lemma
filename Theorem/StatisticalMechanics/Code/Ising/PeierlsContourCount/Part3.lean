/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsContourClose.Part4
import Def.StatisticalMechanics.Code.Ising.PeierlsContourCount.Part2
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


theorem pcc_mem_connClusterFamily {n : ℕ} {K : Finset (Site d)} :
    K ∈ connClusterFamily (d := d) n ↔
      K ∈ clusterFamily (d := d) n ∧ IsConnectedCluster K := by
  unfold connClusterFamily; rw [Finset.mem_filter]


theorem pcc_connFamily_subset_originFamily (n : ℕ) :
    connClusterFamily (d := d) n ⊆ originClusterFamily (d := d) n := by
  intro K hK
  rw [pcc_mem_connClusterFamily] at hK
  rw [pcc_mem_originClusterFamily]
  exact ⟨hK.1, hK.2.1⟩


theorem pcc_walk_transfer {σ : ConfigSpace (Site d)} {o : Site d} :
    ∀ {a x : Site d}, (minusGraph σ).Walk a x → a ∈ minusCluster σ o →
      (latticeOn (minusCluster σ o)).Reachable a x := by
  intro a x w
  induction w with
  | nil => intro _; exact Reachable.refl _
  | @cons a b c hab w ih =>
    intro ha
    have hbcluster : b ∈ minusCluster σ o :=
      (show (minusGraph σ).Reachable o a from ha).trans hab.reachable
    exact (show (latticeOn (minusCluster σ o)).Adj a b
      from ⟨hab.1, ha, hbcluster⟩).reachable.trans (ih hbcluster)


theorem pcc_minusClusterFinset_isConnected {n : ℕ} (τ : {x // x ∈ box d n} → Bool)
    (ho : glue (plusField d) τ (origin d) = false) :
    IsConnectedCluster (minusClusterFinset τ ho) := by
  refine ⟨?_, ?_⟩
  · rw [minusClusterFinset, Set.Finite.mem_toFinset]; exact origin_mem_minusCluster (origin d)
  · intro x hx
    rw [minusClusterFinset, Set.Finite.mem_toFinset] at hx
    rw [minusClusterFinset_coe τ ho]
    exact pcc_walk_transfer (Classical.choice hx) (origin_mem_minusCluster (origin d))


theorem pcc_minusClusterFinset_mem_connFamily {n : ℕ} (τ : {x // x ∈ box d n} → Bool)
    (ho : glue (plusField d) τ (origin d) = false) :
    minusClusterFinset τ ho ∈ connClusterFamily (d := d) n := by
  rw [pcc_mem_connClusterFamily]
  exact ⟨minusClusterFinset_mem_family τ ho, pcc_minusClusterFinset_isConnected τ ho⟩


theorem pcc_probOriginMinus_le_sum_conn (n : ℕ) (β : ℝ) :
    probOriginMinus (plusField d) n (bondFinsetTouch d n) β 0
      ≤ ∑ K ∈ connClusterFamily (d := d) n,
          probContour (↑K) (plusField d) n (bondFinsetTouch d n) β := by
  classical
  unfold probOriginMinus probContour
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun τ _ => ?_)
  set g : Finset (Site d) → ℝ := fun K =>
    (if ContourEvent (↑K) (bondFinsetTouch d n) (glue (plusField d) τ)
      then fvProb (plusField d) n (bondFinsetTouch d n) β 0 τ else 0) with hg
  have hgnn : ∀ K ∈ connClusterFamily (d := d) n, 0 ≤ g K := by
    intro K _; rw [hg]; dsimp only; split
    · exact fvProb_nonneg _ _ _ _ _ _
    · exact le_refl 0
  by_cases ho : glue (plusField d) τ (origin d) = false
  · rw [if_pos ho]
    have hKmem : minusClusterFinset τ ho ∈ connClusterFamily (d := d) n :=
      pcc_minusClusterFinset_mem_connFamily τ ho
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


theorem pcc_probOriginMinus_le_sum_exp_conn (n : ℕ) (β : ℝ) :
    probOriginMinus (plusField d) n (bondFinsetTouch d n) β 0
      ≤ ∑ K ∈ connClusterFamily (d := d) n,
          Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch d n) : ℝ)) := by
  refine le_trans (pcc_probOriginMinus_le_sum_conn n β) ?_
  apply Finset.sum_le_sum
  intro K hK
  have hKfam : K ∈ clusterFamily (d := d) n := (pcc_mem_connClusterFamily.mp hK).1
  have hKbox : (↑K : Set (Site d)) ⊆ box d n := clusterFamily_subset_box hKfam
  have hbound := contour_energy_bound n (↑K) hKbox (plusField d) (bondFinsetTouch d n) β
  exact hbound


end Ising
end StatMech
