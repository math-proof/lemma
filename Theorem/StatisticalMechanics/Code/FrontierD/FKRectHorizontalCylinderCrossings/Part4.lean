/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderLaw.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderCrossings.Part4
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectHorizontalCylinderCrossingTarget_reachable
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    {x : Fin R.width}
    (hx : FKRectHorizontalCylinderCrossingSource R rho x) :
    (FK.openSub (fkRectHorizontalCylinderGraph R) rho).Reachable
      (x, fkRectBottomRow R)
      (fkRectHorizontalCylinderCrossingTarget R rho x,
        fkRectTopRow R) := by
  classical
  rw [fkRectHorizontalCylinderCrossingTarget, dif_pos hx]
  exact Classical.choose_spec hx


end
end StatMech.FrontierD
