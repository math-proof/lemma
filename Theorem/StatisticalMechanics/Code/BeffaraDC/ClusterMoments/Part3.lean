/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterMoments.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.TreePercolation.Part6
import Def.StatisticalMechanics.Code.BeffaraDC.ClusterMoments.Part2
open scoped BigOperators
open Set Filter Topology


namespace StatMech

namespace BeffaraDC

open StatMech.Percolation


theorem clusterMoment_lt_top_of_subcriticalDomination {dist : ℕ → ℝ} {C r : ℝ}
    (hnn : ∀ n, 0 ≤ dist n) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (htail : ∀ n, dist n ≤ C * r ^ n) (d : ℕ) :
    clusterMoment dist d ≤ ∑' n : ℕ, (n : ℝ) ^ d * (C * r ^ n) :=
  (clusterSizeDomination_of_geometricTail hnn hr0 hr1 htail).allMoments_lt_top d

end BeffaraDC
end StatMech
