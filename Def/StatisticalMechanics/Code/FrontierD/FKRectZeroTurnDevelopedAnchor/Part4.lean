/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedOpenBoundaryDependence
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedAnchor.Part4
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectRawPrimalCrossingDevelopedHeight
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (y : R.Vertex) : Int :=
  (y.2.val : Int) + (R.height : Int) *
    fkRectRawPrimalCrossingVerticalPotential R omega X y


noncomputable def fkRectRawPrimalCrossingTorusVertices
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    Finset R.Vertex := by
  classical
  exact Finset.univ.filter fun y =>
    (fkRectOpenGraph R omega).connectedComponentMk y =
      fkRectRawPrimalCrossingTorusComponent R omega X

end
end StatMech.FrontierD
