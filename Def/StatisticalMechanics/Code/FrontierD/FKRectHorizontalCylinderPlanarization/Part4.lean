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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderPlanarization.Part4
open Finset SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def fkRectHorizontalCylinderUnexploredLiftSite
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (x : FKRectHorizontalCylinderUnexploredVertex R rho S) : Site 2 :=
  fkRectSquareSiteOfPair (fkRectSquareDevelopPoint
    (fkRectHorizontalCylinderUnexploredLiftPoint R rho S x))

end
end StatMech.FrontierD
