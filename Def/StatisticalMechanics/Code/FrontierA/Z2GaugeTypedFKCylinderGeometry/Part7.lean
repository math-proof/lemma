module
public import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinder.Part4
public import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinderGeometry.Part6
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

noncomputable section

def centralUpperLayerVertices (n : Nat) : Finset
    (CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) :=
  (Finset.univ : Finset
      (Fin (centralSquareSide n) × Fin (centralSquareSide n))).image
    (fun xy => some (CubicalCell.mk xy.1 xy.2 (centralUpperZ n)))

end
end StatMech.FrontierA
