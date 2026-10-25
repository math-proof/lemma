/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusCrossingEvents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterEventFKG.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectVertexRectangle (R : FKRectTorus)
    (x0 x1 y0 y1 : Nat) : Set R.Vertex :=
  {v | x0 ≤ v.1.val ∧ v.1.val ≤ x1 ∧
    y0 ≤ v.2.val ∧ v.2.val ≤ y1}


def fkRectVerticalCrossingEvent (R : FKRectTorus)
    (x0 x1 y0 y1 : Nat) : Set R.Configuration :=
  {omega | ∃ (x y : fkRectVertexRectangle R x0 x1 y0 y1),
    x.1.2.val = y0 ∧ y.1.2.val = y1 ∧
      FKRectConnectedWithin R omega
        (fkRectVertexRectangle R x0 x1 y0 y1) x y}


def fkRectHorizontalCrossingEvent (R : FKRectTorus)
    (x0 x1 y0 y1 : Nat) : Set R.Configuration :=
  {omega | ∃ (x y : fkRectVertexRectangle R x0 x1 y0 y1),
    x.1.1.val = x0 ∧ y.1.1.val = x1 ∧
      FKRectConnectedWithin R omega
        (fkRectVertexRectangle R x0 x1 y0 y1) x y}

end
end StatMech.FrontierD
