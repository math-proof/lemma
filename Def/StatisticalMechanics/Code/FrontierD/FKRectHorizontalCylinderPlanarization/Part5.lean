module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderExploration
public import Theorem.StatisticalMechanics.Code.FrontierD.FKFreeConnectionBoxEmbedding
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingEvent.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulHorizontalExtension
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulCarrierDisjoint
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulShearCoordinates
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulWalkVerticalBound
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDisjointWinding.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderPlanarization.Part5
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

noncomputable def fkRectHorizontalCylinderUnexploredLiftRadius
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) : Nat :=
  Finset.univ.sup fun x : FKRectHorizontalCylinderUnexploredVertex R rho S =>
    max ((fkRectHorizontalCylinderUnexploredLiftSite R rho S x 0).natAbs)
      ((fkRectHorizontalCylinderUnexploredLiftSite R rho S x 1).natAbs)

end
end StatMech.FrontierD
