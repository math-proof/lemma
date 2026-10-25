/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangHalfPlaneDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.HolomorphicFamilyEquicontinuity
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangRealAnchor.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangHalfPlaneDiagonal
open Filter Metric Set Topology
open scoped UniformConvergence


namespace StatMech.FrontierA

open StatMech.FK


def rightHalfPlaneCompact (n : ℕ) : Set ℂ :=
  closedBall 0 (n + 1 : ℝ) ∩ {z : ℂ | (1 : ℝ) / (n + 1) ≤ z.re}

end StatMech.FrontierA
