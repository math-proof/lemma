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
import Def.StatisticalMechanics.Code.BeffaraDC.ClusterDomination.Part2
open scoped BigOperators NNReal ENNReal
open Set Filter Topology MeasureTheory


namespace StatMech

namespace BeffaraDC

open StatMech.Percolation StatMech.Lattice

variable {d : ℕ}


theorem clusterSizeLargeEvent_subset_crossing (n : ℕ) :
    clusterSizeLargeEvent d n ⊆ crossingEvent d n :=
  fun _ hω => clusterSize_large_subset_crossing n _ hω


theorem clusterSizeLargeProb_le_crossProb (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (clusterSizeLargeEvent d n)
      ≤ crossProb d p hp n :=
  measureReal_mono (clusterSizeLargeEvent_subset_crossing n) (measure_ne_top _ _)


theorem clusterSizeTail_geometricTail (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (hphi : phi d p hp S < 1)
    (L : ℕ) (hL : 1 ≤ L) (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) :
    ∃ C, 0 < C ∧ ∃ r, 0 < r ∧ r < 1 ∧
      ∀ n, (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
              (clusterSizeLargeEvent d n)
            ≤ C * r ^ n := by
  obtain ⟨C, hC, r, hr0, hr1, hgeo⟩ :=
    crossProb_geometricTail p hp S hoS hphi L hL hSbox
  refine ⟨C, hC, r, hr0, hr1, fun n => ?_⟩
  exact le_trans (clusterSizeLargeProb_le_crossProb p hp n) (hgeo n)


end BeffaraDC
end StatMech
