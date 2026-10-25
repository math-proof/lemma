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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderPlanarization.Part3
open Finset SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def fkRectHorizontalCylinderUnexploredRootWalk
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (x : FKRectHorizontalCylinderUnexploredVertex R rho S) :
    (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
      (fkRectHorizontalCylinderBottomRoots R S)).Walk
        (fkRectHorizontalCylinderUnexploredComponentRoot R rho S x) x :=
  Classical.choice (SimpleGraph.ConnectedComponent.exact
    (fkRectHorizontalCylinderUnexploredComponentRoot_component R rho S x))


noncomputable def fkRectHorizontalCylinderUnexploredLiftPoint
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (x : FKRectHorizontalCylinderUnexploredVertex R rho S) : Int × Int :=
  let root := fkRectHorizontalCylinderUnexploredComponentRoot R rho S x
  let p : Int × Int := ((root.1.1.val : Int), (root.1.2.val : Int))
  p + fkRectWalkDevelopedDisplacement R
    ((fkRectHorizontalCylinderUnexploredRootWalk R rho S x).map
      (fkRectHorizontalCylinderUnexploredInclusion R rho S))

end
end StatMech.FrontierD
