/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHardCrossingOrientationNoGo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCrossingAlgebra
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHardCrossingOrientationNoGo


namespace StatMech.FrontierD

def FKRectWideCrossingReverseOrientationBridge
    (q hard easy : Real) : Prop :=
  easy ^ 2 / (1 + q ^ 2) <= hard


end StatMech.FrontierD
