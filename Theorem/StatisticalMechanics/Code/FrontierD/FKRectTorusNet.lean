/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusEulerDefect.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusNet
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectCrossesHorizontalSeam_mk
    (R : FKRectTorus) (x y : R.Vertex) :
    fkRectCrossesHorizontalSeam R s(x, y) ↔
      (x.1.val = 0 ∧ y.1.val + 1 = R.width) ∨
        (y.1.val = 0 ∧ x.1.val + 1 = R.width) := Iff.rfl

@[simp] theorem fkRectCrossesVerticalSeam_mk
    (R : FKRectTorus) (x y : R.Vertex) :
    fkRectCrossesVerticalSeam R s(x, y) ↔
      (x.2.val = 0 ∧ y.2.val + 1 = R.height) ∨
        (y.2.val = 0 ∧ x.2.val + 1 = R.height) := Iff.rfl


end
end StatMech.FrontierD
