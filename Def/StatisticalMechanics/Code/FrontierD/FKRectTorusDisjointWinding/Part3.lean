/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDisjointWinding.Part2
open SimpleGraph


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

def fkRectSquareCoverPointVertex (R : FKRectTorus)
    (p : ZMod (fkRectSquareCoverSide R) ×
      ZMod (fkRectSquareCoverSide R)) : R.Vertex :=
  fkRectSquareRepresentativeVertex R
    ((p.1.val : Int), (p.2.val : Int))

end
end StatMech.FrontierD
