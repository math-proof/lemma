/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusEulerDefect.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectCrossesHorizontalSeam (R : FKRectTorus)
    (e : Sym2 R.Vertex) : Prop :=
  Sym2.lift ⟨fun x y =>
    (x.1.val = 0 ∧ y.1.val + 1 = R.width) ∨
      (y.1.val = 0 ∧ x.1.val + 1 = R.width), by
        intro x y
        apply propext
        tauto⟩ e


def fkRectCrossesVerticalSeam (R : FKRectTorus)
    (e : Sym2 R.Vertex) : Prop :=
  Sym2.lift ⟨fun x y =>
    (x.2.val = 0 ∧ y.2.val + 1 = R.height) ∨
      (y.2.val = 0 ∧ x.2.val + 1 = R.height), by
        intro x y
        apply propext
        tauto⟩ e

end
end StatMech.FrontierD
