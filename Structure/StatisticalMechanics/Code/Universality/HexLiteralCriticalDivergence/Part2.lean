/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCriticalDivergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCoefficientAggregation.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexColumnMembershipClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorPairFromReflection.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCriticalDivergence.Part3


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


structure HexLiteralSideLimits (a : ℂ) (h0 : ℤ) (tau : ℕ → ℝ) where
  fibers : HexLiteralSideFibers a h0
  tendsto_tau : ∀ T,
    Filter.Tendsto (fibers.columnEmb T).fiberSum
      Filter.atTop (nhds (tau T))


end StatMech.Universality
