/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHardCrossingOrientationNoGo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCrossingAlgebra


namespace StatMech.FrontierD

structure FKRectWideCrossingScalarData
    (q hard easy : Real) : Prop where
  hard_nonneg : 0 <= hard
  hard_le_one : hard <= 1
  easy_nonneg : 0 <= easy
  easy_le_one : easy <= 1
  squareSeed : 1 / (1 + q) <= easy
  dualCover : 1 <= easy + q ^ 2 * hard
  sameOrientationQuadratic : hard ^ 2 / (1 + q ^ 2) <= easy


end StatMech.FrontierD
