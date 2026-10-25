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
import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer
open Finset Matrix Filter Topology
open scoped BigOperators


namespace StatMech.Ising

noncomputable section

def rectangularPrismSiteEquiv (m n h : Nat) :
    RectangularPrismSite m n h ≃
      Fin m × Fin n × Fin (2 * h + 1) where
  toFun v := (v.x, v.y, v.z)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv v := by cases v; rfl
  right_inv p := by rcases p with ⟨x, y, z⟩; rfl

end
end StatMech.Ising
