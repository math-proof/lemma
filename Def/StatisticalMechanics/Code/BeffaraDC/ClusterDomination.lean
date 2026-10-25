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
import Theorem.StatisticalMechanics.Code.BeffaraDC.ClusterDomination
open scoped BigOperators NNReal ENNReal
open Set Filter Topology MeasureTheory


namespace StatMech

namespace BeffaraDC

open StatMech.Percolation StatMech.Lattice

variable {d : ℕ}


noncomputable def clusterRadiusDomination (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (hphi : phi d p hp S < 1)
    (L : ℕ) (hL : 1 ≤ L) (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) :
    ClusterSizeDomination :=
  let h := crossProb_geometricTail p hp S hoS hphi L hL hSbox
  clusterSizeDomination_of_geometricTail (dist := fun n => crossProb d p hp n)
    (C := h.choose) (r := h.choose_spec.2.choose)
    (fun n => crossProb_nonneg d p hp n)
    h.choose_spec.2.choose_spec.1.le
    h.choose_spec.2.choose_spec.2.1
    h.choose_spec.2.choose_spec.2.2

end BeffaraDC
end StatMech
