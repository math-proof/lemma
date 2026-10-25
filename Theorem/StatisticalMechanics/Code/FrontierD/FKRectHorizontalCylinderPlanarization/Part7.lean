/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderPlanarization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderExploration
import Theorem.StatisticalMechanics.Code.FrontierD.FKFreeConnectionBoxEmbedding
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingEvent.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulHorizontalExtension
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulCarrierDisjoint
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulShearCoordinates
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulWalkVerticalBound
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDisjointWinding.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderPlanarization.Part6
open Finset SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem fkRectHorizontalCylinderUnexploredBoxEmbedding_injective
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) :
    Function.Injective
      (fkRectHorizontalCylinderUnexploredBoxEmbedding R rho S) := by
  intro x y hxy
  apply fkRectHorizontalCylinderUnexploredLiftSite_injective R rho S
  exact congrArg Subtype.val hxy

theorem fkRectHorizontalCylinderUnexploredBox_adjMatch
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (hno : FKRectHorizontalCylinderUnexploredNoHorizontalWinding R rho S) :
    FK.ocd_AdjMatch
      (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
        (fkRectHorizontalCylinderBottomRoots R S))
      (FK.boxGraph 2
        (fkRectHorizontalCylinderUnexploredLiftRadius R rho S))
      (fkRectHorizontalCylinderUnexploredBoxEmbedding R rho S) := by
  intro x y
  constructor
  · intro hxy
    exact fkRectHorizontalCylinderUnexploredLiftSite_adj_of_adj
      R rho S hno hxy
  · intro hxy
    exact fkRectHorizontalCylinderUnexplored_adj_of_liftSite_adj
      R rho S hxy


end
end StatMech.FrontierD
