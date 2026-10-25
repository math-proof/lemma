/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonTurning.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardCycleCoefficient.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonTurning
open scoped BigOperators


namespace StatMech.FrontierA

def kwComplexCross (x y : ℂ) : ℝ :=
  x.re * y.im - x.im * y.re

end StatMech.FrontierA
