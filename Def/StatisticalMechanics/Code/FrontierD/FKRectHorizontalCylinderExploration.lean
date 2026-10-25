/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderExploration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderCrossings.Part6
import Theorem.StatisticalMechanics.Code.FK.ClusterExplorationFreeBoundary
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectHorizontalCylinderBottomRoots
    (R : FKRectTorus) (S : Finset (Fin R.width)) : Finset R.Vertex :=
  S.image fun x => (x, fkRectBottomRow R)


def FKRectHorizontalCylinderExploredVertex
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) (v : R.Vertex) : Prop :=
  FK.ClusterExploredVertex (fkRectHorizontalCylinderGraph R) rho
    (fkRectHorizontalCylinderBottomRoots R S) v


def FKRectHorizontalCylinderUnexploredVertex
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) :=
  FK.ClusterUnexploredVertex (fkRectHorizontalCylinderGraph R) rho
    (fkRectHorizontalCylinderBottomRoots R S)

end
end StatMech.FrontierD
