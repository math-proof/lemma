/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDevelopedWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part2


namespace StatMech.FrontierD

noncomputable section

def fkRectSquareDevelopEquiv : (Int × Int) ≃ (Int × Int) where
  toFun := fkRectSquareDevelopPoint
  invFun := fkRectSquareUndevelopPoint
  left_inv := fkRectSquareUndevelopPoint_developPoint
  right_inv := fkRectSquareDevelopPoint_undevelopPoint


def fkRectLiftedIndexedEdgeEnds (R : FKRectTorus) (e : R.EdgeIndex) :
    (Int × Int) × (Int × Int) :=
  let X : Int := e.2.1.val
  let Y : Int := e.2.2.val
  if e.1 then
    ((X, Y), (X, Y - 1))
  else if Even e.2.2.val then
    ((X, Y), (X - 1, Y - 1))
  else
    ((X - 1, Y), (X, Y - 1))


end
end StatMech.FrontierD
