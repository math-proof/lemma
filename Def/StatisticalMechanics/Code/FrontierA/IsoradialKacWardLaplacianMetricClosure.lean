/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacianMetricClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardMetricClosure.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacianAtlas
import Structure.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacianMetricClosure
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

universe u

variable {V E D Component : Type*}
  [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
  [Fintype D] [DecidableEq D]
  [Fintype Component] [DecidableEq Component]


namespace IsoradialMetricComponentOrientationData

noncomputable def toComponentIdentification
    (R : RibbonPermutationSystem E D)
    (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (weight : E -> Complex) (conductance transport : V -> V -> Complex)
    (genus_le_one : C.genus ≤ 1)
    (data : IsoradialMetricComponentOrientationData Component
      R character weight conductance transport) :
    GenusZeroOneRibbonComponentIdentification Component
      R C character weight conductance transport where
  genus_le_one := genus_le_one
  outgoingEdgeSet := data.outgoingEdgeSet
  conductanceMonomial := data.conductanceMonomial
  supported := data.supported
  components := data.components
  componentHolonomy := data.componentHolonomy
  boundaryCoefficient_supported := data.boundaryCoefficient_supported
  boundaryCoefficient_unsupported := data.boundaryCoefficient_unsupported
  fiberEmpty_unsupported := data.fiberEmpty_unsupported
  fiberEquivOrientations := fun F hF =>
    { toFun := data.orientationOf F hF
      invFun := data.outgoingOfOrientation F hF
      left_inv := data.outgoingOf_orientationOf F hF
      right_inv := data.orientationOf_outgoingOf F hF }
  formanFactor_orientation := data.formanFactor_orientation

end IsoradialMetricComponentOrientationData
end StatMech.FrontierA
