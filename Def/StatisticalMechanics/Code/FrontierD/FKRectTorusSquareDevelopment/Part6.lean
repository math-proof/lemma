/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDevelopedWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Abbrev.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment


namespace StatMech.FrontierD

noncomputable section

def fkRectVertexSquarePoint (R : FKRectTorus) (x : R.Vertex) : Int × Int :=
  fkRectSquareDevelopPoint (x.1.val, x.2.val)


def fkRectVertexSquareClass (R : FKRectTorus) (x : R.Vertex) :
    FKRectSquareTorus R :=
  QuotientAddGroup.mk (fkRectVertexSquarePoint R x)


end
end StatMech.FrontierD
