/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinder.Part4
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinderGeometry.Part7
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

theorem cubicalXYSheetUpperVertices_central_eq (n : Nat) :
    cubicalXYSheetUpperVertices
        (a := centralSquareSide n) (b := centralSquareSide n)
        (c := centralSquareSide n + centralSquareSide n)
        (centralSquareSheetHeight n) =
      centralUpperLayerVertices n := by
  rw [cubicalXYSheetUpperVertices_eq_layer]
  · unfold centralUpperLayerVertices
    apply Finset.image_congr
    intro xy _
    congr 2
  · simp [centralSquareSheetHeight, centralSquareSide]
  · simp [centralSquareSheetHeight, centralSquareSide]


end
end StatMech.FrontierA
