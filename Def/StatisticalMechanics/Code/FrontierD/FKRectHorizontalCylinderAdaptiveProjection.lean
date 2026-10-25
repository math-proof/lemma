/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderAdaptiveProjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ClusterAdaptiveProjection.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderExploration
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectHorizontalCylinderAdaptiveInsideEdges
    (R : FKRectTorus) (S : Finset (Fin R.width))
    (rho : ConfigSpace (Sym2 R.Vertex)) : Finset (Sym2 R.Vertex) :=
  FK.clusterAdaptiveInsideEdges (fkRectHorizontalCylinderGraph R)
    (fkRectHorizontalCylinderBottomRoots R S) rho


def fkRectHorizontalCylinderAdaptiveProjection
    (R : FKRectTorus) (S : Finset (Fin R.width))
    (rho : ConfigSpace (Sym2 R.Vertex)) : ConfigSpace (Sym2 R.Vertex) :=
  FK.clusterAdaptiveProjection (fkRectHorizontalCylinderGraph R)
    (fkRectHorizontalCylinderBottomRoots R S) rho

end
end StatMech.FrontierD
