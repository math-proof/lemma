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
import Def.StatisticalMechanics.Code.BeffaraDC.ClusterDomination.Part3
open scoped BigOperators NNReal ENNReal
open Set Filter Topology MeasureTheory


namespace StatMech

namespace BeffaraDC

open StatMech.Percolation StatMech.Lattice

variable {d : ℕ}


theorem clusterSizeMoment_lt_top (p : NNReal) (hp : p ≤ 1) (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (hphi : phi d p hp S < 1)
    (L : ℕ) (hL : 1 ≤ L) (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) (d' : ℕ) :
    ∃ C r, 0 ≤ r ∧ r < 1 ∧
      clusterMoment (fun n => (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
            (clusterSizeLargeEvent d n)) d'
        ≤ ∑' n : ℕ, (n : ℝ) ^ d' * (C * r ^ n) := by
  set D := clusterSizeDomination p hp S hoS hphi L hL hSbox with hD
  refine ⟨D.const, D.rate, D.rate_nonneg, D.rate_lt_one, ?_⟩
  have := D.allMoments_lt_top d'
  simpa [hD] using this

end BeffaraDC
end StatMech
