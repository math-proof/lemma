/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.CylinderPathExpansion
import Theorem.StatisticalMechanics.Code.Ising.CenterMarkedPath.Part2
import Theorem.StatisticalMechanics.Code.Ising.PositiveTransferCenterObservable
import Theorem.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushinSpinFlip.Part3
import Abbrev.StatisticalMechanics.Code.Ising.RectangularPrismTransfer
open Finset Matrix Filter Topology
open scoped BigOperators


namespace StatMech.Ising

noncomputable section

def rectangularPrismLayer {m n h : Nat}
    (sigma : RectangularPrismConfig m n h) (z : Fin (2 * h + 1)) :
    RectangularLayerConfig m n :=
  fun p => sigma ⟨p.1, p.2, z⟩


def rectangularPrismLayerEquiv (m n h : Nat) :
    RectangularPrismConfig m n h ≃
      (Fin (2 * h + 1) -> RectangularLayerConfig m n) where
  toFun := rectangularPrismLayer
  invFun q := fun v => q v.z (v.x, v.y)
  left_inv sigma := by
    funext v
    rfl
  right_inv q := by
    funext z p
    rfl

end
end StatMech.Ising
