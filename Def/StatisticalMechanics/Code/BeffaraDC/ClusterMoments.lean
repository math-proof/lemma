/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterMoments.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.TreePercolation.Part6
open scoped BigOperators
open Set Filter Topology


namespace StatMech

namespace BeffaraDC

noncomputable def clusterMoment (dist : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑' n : ℕ, (n : ℝ) ^ d * dist n


end BeffaraDC
end StatMech
