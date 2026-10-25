/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterMoments.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.TreePercolation.Part6
import Theorem.StatisticalMechanics.Code.BeffaraDC.ClusterMoments
open scoped BigOperators
open Set Filter Topology


namespace StatMech

namespace BeffaraDC

structure ClusterSizeDomination where
  
  dist : ℕ → ℝ
  
  const : ℝ
  
  rate : ℝ
  
  nonneg : ∀ n, 0 ≤ dist n
  
  rate_nonneg : 0 ≤ rate
  
  rate_lt_one : rate < 1
  
  geometricTail : ∀ n, dist n ≤ const * rate ^ n

end BeffaraDC
end StatMech
