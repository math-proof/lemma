/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderLaw.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderCrossings
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def FKRectHorizontalCylinderCrossingSource
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (x : Fin R.width) : Prop :=
  ∃ y : Fin R.width,
    (FK.openSub (fkRectHorizontalCylinderGraph R) rho).Reachable
      (x, fkRectBottomRow R) (y, fkRectTopRow R)


noncomputable def fkRectHorizontalCylinderCrossingRepresentative
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (C : {C :
      (FK.openSub (fkRectHorizontalCylinderGraph R) rho).ConnectedComponent //
        FKRectHorizontalCylinderCrossingComponent R rho C}) : Fin R.width :=
  Classical.choose C.2.1

end
end StatMech.FrontierD
