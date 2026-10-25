/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinder.Part4
import Abbrev.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinderGeometry
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

def centralSquareSheetHeight (n : Nat) :
    Fin (centralSquareSide n + centralSquareSide n + 1) :=
  ⟨centralSquareSide n, by omega⟩

def centralLowerZ {n : Nat} (z : Fin (centralSquareSide n)) :
    Fin (centralSquareSide n + centralSquareSide n) :=
  Fin.castLE (by omega) z

end
end StatMech.FrontierA
