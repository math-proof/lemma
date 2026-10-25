/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangHalfPlaneDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.HolomorphicFamilyEquicontinuity
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangRealAnchor.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangHalfPlaneDiagonal.Part2
open Filter Metric Set Topology
open scoped UniformConvergence


namespace StatMech.FrontierA

open StatMech.FK


def rightHalfPlaneCompactExhaustion :
    CompactExhaustion {z : ℂ | 0 < z.re} where
  sets := rightHalfPlaneCompact
  isCompact := rightHalfPlaneCompact_isCompact
  subset := rightHalfPlaneCompact_subset
  cofinal := rightHalfPlaneCompact_cofinal


def leftHalfPlaneCompact (n : ℕ) : Set ℂ :=
  closedBall 0 (n + 1 : ℝ) ∩ {z : ℂ | z.re ≤ -((1 : ℝ) / (n + 1))}

end StatMech.FrontierA
