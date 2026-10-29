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
open scoped BigOperators NNReal ENNReal
open Set Filter Topology MeasureTheory


namespace StatMech

namespace BeffaraDC

open StatMech.Percolation StatMech.Lattice

variable {d : ℕ}


theorem geometricTail_of_expDecay {f : ℕ → ℝ} {C c : ℝ} (hc : 0 < c)
    (hf : ∀ n, f n ≤ C * Real.exp (-c * n)) :
    ∃ r, 0 < r ∧ r < 1 ∧ ∀ n, f n ≤ C * r ^ n := by
  refine ⟨Real.exp (-c), Real.exp_pos _, ?_, fun n => ?_⟩
  · rw [Real.exp_lt_one_iff]; linarith
  · have hrw : Real.exp (-c * n) = Real.exp (-c) ^ n := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [← hrw]; exact hf n


theorem crossProb_geometricTail (p : NNReal) (hp : p ≤ 1) (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (hphi : phi d p hp S < 1)
    (L : ℕ) (hL : 1 ≤ L) (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) :
    ∃ C, 0 < C ∧ ∃ r, 0 < r ∧ r < 1 ∧
      ∀ n, crossProb d p hp n ≤ C * r ^ n := by
  obtain ⟨c, hc, C, hC, hbound⟩ :=
    subcritical_decay_unconditional p hp S hoS hphi L hL hSbox
  obtain ⟨r, hr0, hr1, hgeo⟩ := geometricTail_of_expDecay hc hbound
  exact ⟨C, hC, r, hr0, hr1, hgeo⟩


end BeffaraDC
end StatMech
