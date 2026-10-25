/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetTiling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetPositionReduction
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetTiling
open Finset
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

def tripleTileSide (n : Nat) : Nat := 2 * n + 1

def tripleTiledSide (n : Nat) : Nat := 2 * (3 * n + 1) + 1

def tripleCentralHeight (n : Nat) : Nat := 3 * n + 2

def tripleCentralHeightFin (n : Nat) : Fin (tripleTiledSide n + 1) :=
  ⟨tripleCentralHeight n, by
    simp only [tripleCentralHeight, tripleTiledSide, tripleTileSide]
    omega⟩

end
end StatMech.FrontierA
