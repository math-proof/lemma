module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderExploration
public import Theorem.StatisticalMechanics.Code.FrontierD.FKFreeConnectionBoxEmbedding
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingEvent.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulHorizontalExtension
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulCarrierDisjoint
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulShearCoordinates
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulWalkVerticalBound
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDisjointWinding.Part4
public import Structure.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderPlanarization
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

noncomputable def FKRectHorizontalCylinderUnexploredPlanarization.ofNoWinding
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (hno : FKRectHorizontalCylinderUnexploredNoHorizontalWinding R rho S) :
    FKRectHorizontalCylinderUnexploredPlanarization R rho S where
  radius := fkRectHorizontalCylinderUnexploredLiftRadius R rho S
  embedding := fkRectHorizontalCylinderUnexploredBoxEmbedding R rho S
  injective :=
    fkRectHorizontalCylinderUnexploredBoxEmbedding_injective R rho S
  adjMatch := fkRectHorizontalCylinderUnexploredBox_adjMatch R rho S hno


noncomputable def FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (pair : Fin R.width → Fin R.width) (S : Finset (Fin R.width))
    (hS : S.Nonempty)
    (hW : FKRectHorizontalCylinderDistinctPairedWitness R pair S rho) :
    FKRectHorizontalCylinderUnexploredPlanarization R rho S :=
  .ofNoWinding R rho S
    (fkRectHorizontalCylinder_noHorizontalWinding_of_pairedWitness
      R rho pair S hS hW)


end
end StatMech.FrontierD
