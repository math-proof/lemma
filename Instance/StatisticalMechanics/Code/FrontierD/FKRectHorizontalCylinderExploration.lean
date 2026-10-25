/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderExploration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderCrossings.Part6
import Theorem.StatisticalMechanics.Code.FK.ClusterExplorationFreeBoundary
import Def.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderExploration
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable instance instFintypeFKRectHorizontalCylinderUnexploredVertex
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) :
    Fintype (FKRectHorizontalCylinderUnexploredVertex R rho S) :=
  FK.instFintypeClusterUnexploredVertex
    (fkRectHorizontalCylinderGraph R) rho
    (fkRectHorizontalCylinderBottomRoots R S)

noncomputable instance instDecidableEqFKRectHorizontalCylinderUnexploredVertex
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) :
    DecidableEq (FKRectHorizontalCylinderUnexploredVertex R rho S) :=
  Classical.decEq _

end
end StatMech.FrontierD
