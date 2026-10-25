/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingPrimitiveArithmetic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNet.Part3


namespace StatMech.FrontierD

def FKRectPrimitiveWinding (w : Int × Int) : Prop :=
  ∃ a b : Int, a * w.1 + b * w.2 = 1


end StatMech.FrontierD
