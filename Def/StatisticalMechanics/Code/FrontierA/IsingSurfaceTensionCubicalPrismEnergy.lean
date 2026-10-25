/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismEnergy.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetGauge


namespace StatMech.FrontierA

open scoped BigOperators symmDiff

open Filter Topology

open StatMech StatMech.Ising

noncomputable section

def oddCubicalCellEquivPrismSite (n : Nat) :
    CubicalCell (2 * n + 1) (2 * n + 1) (2 * n + 1) ≃
      RectangularPrismSite (2 * n + 1) (2 * n + 1) n where
  toFun q := ⟨q.x, q.y, q.z⟩
  invFun v := ⟨v.x, v.y, v.z⟩
  left_inv q := by cases q; rfl
  right_inv v := by cases v; rfl


def oddCubicalAnchoredEquivPrismConfig (n : Nat) :
    AnchoredConfig
        (CubicalDualVertex (2 * n + 1) (2 * n + 1) (2 * n + 1)) none ≃
      RectangularPrismConfig (2 * n + 1) (2 * n + 1) n where
  toFun s v := !s.1 (some ((oddCubicalCellEquivPrismSite n).symm v))
  invFun sigma := ⟨fun q => match q with
    | none => false
    | some v => !sigma (oddCubicalCellEquivPrismSite n v), rfl⟩
  left_inv s := by
    apply Subtype.ext
    funext q
    cases q with
    | none => exact s.2.symm
    | some q => simp
  right_inv sigma := by
    funext v
    simp

end
end StatMech.FrontierA
