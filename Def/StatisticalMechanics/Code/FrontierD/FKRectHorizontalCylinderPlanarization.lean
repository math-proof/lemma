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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderPlanarization
open Finset SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

def fkRectHorizontalCylinderUnexploredInclusion
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) :
    FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
        (fkRectHorizontalCylinderBottomRoots R S) →g
      fkRectHorizontalCylinderGraph R where
  toFun := Subtype.val
  map_rel' := fun h => h


def fkRectHorizontalCylinderUnexploredWalkWinding
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) {x y}
    (p : (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
      (fkRectHorizontalCylinderBottomRoots R S)).Walk x y) : Int × Int :=
  fkRectWalkWinding R
    (p.map (fkRectHorizontalCylinderUnexploredInclusion R rho S))


def FKRectHorizontalCylinderUnexploredNoHorizontalWinding
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) : Prop :=
  ∀ (x : FKRectHorizontalCylinderUnexploredVertex R rho S)
    (p : (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
      (fkRectHorizontalCylinderBottomRoots R S)).Walk x x),
    (fkRectHorizontalCylinderUnexploredWalkWinding R rho S p).1 = 0


def FKRectHorizontalCylinderCrosscutSeparatesHorizontalWinding
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) : Prop :=
  ∀ {x : R.Vertex} (p : (fkRectHorizontalCylinderGraph R).Walk x x),
    (fkRectWalkWinding R p).1 ≠ 0 →
      ∃ v ∈ p.support,
        FKRectHorizontalCylinderExploredVertex R rho S v


end
end StatMech.FrontierD
