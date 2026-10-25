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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderPlanarization.Part7
open Finset SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

structure FKRectHorizontalCylinderUnexploredPlanarization
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) where
  radius : Nat
  embedding : FKRectHorizontalCylinderUnexploredVertex R rho S →
    FK.boxVerts 2 radius
  injective : Function.Injective embedding
  adjMatch : FK.ocd_AdjMatch
    (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
      (fkRectHorizontalCylinderBottomRoots R S))
    (FK.boxGraph 2 radius) embedding


end
end StatMech.FrontierD
