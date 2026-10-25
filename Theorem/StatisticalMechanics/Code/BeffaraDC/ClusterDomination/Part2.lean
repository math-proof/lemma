/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterDomination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.ClusterMoments.Part3
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.Percolation.DctDifferential.Part4
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Def.StatisticalMechanics.Code.BeffaraDC.ClusterDomination
open scoped BigOperators NNReal ENNReal
open Set Filter Topology MeasureTheory


namespace StatMech

namespace BeffaraDC

open StatMech.Percolation StatMech.Lattice

variable {d : ℕ}


@[simp] theorem clusterRadiusDomination_dist (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (hphi : phi d p hp S < 1)
    (L : ℕ) (hL : 1 ≤ L) (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) :
    (clusterRadiusDomination p hp S hoS hphi L hL hSbox).dist
      = fun n => crossProb d p hp n := rfl


theorem clusterRadiusMoment_summable (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (hphi : phi d p hp S < 1)
    (L : ℕ) (hL : 1 ≤ L) (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) (d' : ℕ) :
    Summable (fun n : ℕ => (n : ℝ) ^ d' * crossProb d p hp n) :=
  (clusterRadiusDomination p hp S hoS hphi L hL hSbox).summand_summable d'


theorem clusterRadiusMoment_lt_top (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (hphi : phi d p hp S < 1)
    (L : ℕ) (hL : 1 ≤ L) (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) (d' : ℕ) :
    ∃ C r, 0 ≤ r ∧ r < 1 ∧
      clusterMoment (fun n => crossProb d p hp n) d'
        ≤ ∑' n : ℕ, (n : ℝ) ^ d' * (C * r ^ n) := by
  set D := clusterRadiusDomination p hp S hoS hphi L hL hSbox with hD
  refine ⟨D.const, D.rate, D.rate_nonneg, D.rate_lt_one, ?_⟩
  have := D.allMoments_lt_top d'
  simpa [hD] using this


theorem clusterRadiusMoment_nonneg (p : ℝ≥0) (hp : p ≤ 1) (d' : ℕ) :
    0 ≤ clusterMoment (fun n => crossProb d p hp n) d' :=
  clusterMoment_nonneg (fun n => crossProb_nonneg d p hp n) d'


theorem crossingEvent_eq_cluster_not_subset (n : ℕ)
    (ω : ConfigSpace (Sym2 (Site d))) :
    ω ∈ crossingEvent d n ↔ ¬ (cluster d ω (origin d) ⊆ box d (n - 1)) := by
  rw [mem_crossingEvent]
  constructor
  · rintro ⟨v, hconn, hv⟩ hsub
    exact hv (hsub hconn)
  · intro h
    rw [Set.not_subset] at h
    obtain ⟨v, hv, hvb⟩ := h
    exact ⟨v, hv, hvb⟩


theorem cluster_finite_card_le_of_subset {m : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    (hsub : cluster d ω (origin d) ⊆ box d m) :
    ∃ hfin : (cluster d ω (origin d)).Finite, hfin.toFinset.card ≤ (boxFinset d m).card := by
  refine ⟨(box_finite d m).subset hsub, ?_⟩
  refine Finset.card_le_card (fun y hy => ?_)
  rw [Set.Finite.mem_toFinset] at hy
  rw [mem_boxFinset]
  exact hsub hy


theorem clusterSize_large_subset_crossing (n : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (hsize : ¬ ∃ hfin : (cluster d ω (origin d)).Finite,
        hfin.toFinset.card ≤ (boxFinset d (n - 1)).card) :
    ω ∈ crossingEvent d n := by
  rw [crossingEvent_eq_cluster_not_subset]
  intro hsub
  exact hsize (cluster_finite_card_le_of_subset ω hsub)


theorem clusterSize_le_boxCard_of_finite (ω : ConfigSpace (Sym2 (Site d)))
    (hfin : (cluster d ω (origin d)).Finite) :
    ∃ m, hfin.toFinset.card ≤ (boxFinset d m).card := by
  obtain ⟨m, hm⟩ := finite_subset_box (cluster d ω (origin d)) hfin
  refine ⟨m, Finset.card_le_card (fun y hy => ?_)⟩
  rw [Set.Finite.mem_toFinset] at hy
  rw [mem_boxFinset]
  exact hm hy


end BeffaraDC
end StatMech
