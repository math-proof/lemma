/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismEnergy.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetGauge
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionCubicalPrismEnergy


namespace StatMech.FrontierA

open scoped BigOperators symmDiff

open Filter Topology

open StatMech StatMech.Ising

noncomputable section

def cubicalPlaquetteToOddPrism (n : Nat) :
    CubicalPlaquette (2 * n + 1) (2 * n + 1) (2 * n + 1) ->
      OddPrismTouchIndex n
  | .xy x y z =>
      if hz0 : z.val = 0 then .zZero x y
      else if hz1 : z.val = 2 * n + 1 then .zLast x y
      else .zInternal x y ⟨z.val - 1, by omega⟩
  | .xz x y z =>
      if hy0 : y.val = 0 then .yZero x z
      else if hy1 : y.val = 2 * n + 1 then .yLast x z
      else .yInternal x ⟨y.val - 1, by omega⟩ z
  | .yz x y z =>
      if hx0 : x.val = 0 then .xZero y z
      else if hx1 : x.val = 2 * n + 1 then .xLast y z
      else .xInternal ⟨x.val - 1, by omega⟩ y z

def oddPrismToCubicalPlaquette (n : Nat) :
    OddPrismTouchIndex n ->
      CubicalPlaquette (2 * n + 1) (2 * n + 1) (2 * n + 1)
  | .xInternal x y z => .yz ⟨x.val + 1, by omega⟩ y z
  | .yInternal x y z => .xz x ⟨y.val + 1, by omega⟩ z
  | .zInternal x y z => .xy x y ⟨z.val + 1, by omega⟩
  | .xZero y z => .yz 0 y z
  | .xLast y z => .yz (Fin.last (2 * n + 1)) y z
  | .yZero x z => .xz x 0 z
  | .yLast x z => .xz x (Fin.last (2 * n + 1)) z
  | .zZero x y => .xy x y 0
  | .zLast x y => .xy x y (Fin.last (2 * n + 1))

end
end StatMech.FrontierA
