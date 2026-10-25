/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingGeneration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingInsertion.Part2
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectStepWinding (R : FKRectTorus) (x y : R.Vertex) : Int × Int :=
  (fkRectHorizontalSeamIncrement R x y,
    fkRectVerticalSeamIncrement R x y)

end
end StatMech.FrontierD
