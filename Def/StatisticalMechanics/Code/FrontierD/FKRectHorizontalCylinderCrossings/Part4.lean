/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderLaw.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderCrossings.Part3
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectHorizontalCylinderCrossingTarget
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (x : Fin R.width) : Fin R.width := by
  classical
  exact if h : FKRectHorizontalCylinderCrossingSource R rho x then
      Classical.choose h
    else fkRectLeftColumn R

end
end StatMech.FrontierD
