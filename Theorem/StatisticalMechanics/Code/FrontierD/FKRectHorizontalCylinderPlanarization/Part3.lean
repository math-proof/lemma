module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderExploration
public import Theorem.StatisticalMechanics.Code.FrontierD.FKFreeConnectionBoxEmbedding
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingEvent.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulHorizontalExtension
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulCarrierDisjoint
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulShearCoordinates
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulWalkVerticalBound
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDisjointWinding.Part4
public import Def.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderPlanarization.Part2
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderPlanarization.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem fkRectHorizontalCylinderUnexploredComponentRoot_component
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (x : FKRectHorizontalCylinderUnexploredVertex R rho S) :
    (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
        (fkRectHorizontalCylinderBottomRoots R S)).connectedComponentMk
      (fkRectHorizontalCylinderUnexploredComponentRoot R rho S x) =
    (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
        (fkRectHorizontalCylinderBottomRoots R S)).connectedComponentMk x := by
  exact Quot.out_eq _


end
end StatMech.FrontierD
