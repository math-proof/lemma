/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCutPushforward.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutFreeLaw.Part4
import Instance.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderLaw
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


def fkRectHorizontalCutGraphEdges (R : FKRectTorus) :
    Finset (Sym2 R.Vertex) :=
  (fkRectHorizontalCutEdges R).image (fkRectTorusIndexedEdge R)

end
end StatMech.FrontierD
