/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointCriticalDivergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointAggregation.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointCriticalDivergence.Part2


namespace StatMech.Universality

open HexWalk

noncomputable section

structure HexEndpointSideLimits
    (a : ℂ) (h0 : ℤ) (tau : ℕ → ℝ) where
  fibers : HexEndpointSideFibers a h0
  tendsto_tau : ∀ T,
    Filter.Tendsto (fibers.columnEmb T).fiberSum
      Filter.atTop (nhds (tau T))


end
end StatMech.Universality
