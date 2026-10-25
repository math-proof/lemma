/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardExtremeVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part12


namespace StatMech.FrontierA

def kwComplexDot (x y : ℂ) : ℝ := x.re * y.re + x.im * y.im


noncomputable def kwSupportSlope (u v : ℂ) : ℝ :=
  kwComplexCross u v / (-kwComplexDot u v)

end StatMech.FrontierA
