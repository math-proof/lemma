/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangHalfPlaneDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.HolomorphicFamilyEquicontinuity
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangRealAnchor.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangHalfPlaneDiagonal.Part3
open Filter Metric Set Topology
open scoped UniformConvergence


namespace StatMech.FrontierA

open StatMech.FK


def leftHalfPlaneCompactExhaustion :
    CompactExhaustion {z : ℂ | z.re < 0} where
  sets := leftHalfPlaneCompact
  isCompact := leftHalfPlaneCompact_isCompact
  subset := leftHalfPlaneCompact_subset
  cofinal := leftHalfPlaneCompact_cofinal


end StatMech.FrontierA
