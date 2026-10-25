/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryHorizontalParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib


namespace StatMech.FrontierD

def FKRectHorizontalOddOrZero (u : Int × Int) : Prop :=
  u = 0 ∨ (u.2 = 0 ∧ Odd u.1)

end StatMech.FrontierD
