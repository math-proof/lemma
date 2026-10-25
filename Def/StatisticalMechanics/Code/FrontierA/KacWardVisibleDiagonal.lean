/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVisibleDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardSupportingChord.Part4


namespace StatMech.FrontierA

def kwTriangleBaseHeight (A C P : ℂ) : ℝ :=
  kwComplexCross (C - A) (P - A)

end StatMech.FrontierA
