/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoherentLimit.Part12
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicBridge
open Finset SimpleGraph MeasureTheory


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.FK StatMech.FK.PeriodicPlanar

noncomputable section

noncomputable def fkSquarePeriodicVertexEquiv (n : Nat) :
    square.OrbitVertex n ≃ FK.boxVerts 2 n where
  toFun x := ⟨x.1, by
    exact (fkSquarePeriodic_mem_orbitBox_iff n x.1).mp x.2⟩
  invFun x := ⟨x.1, by
    exact (fkSquarePeriodic_mem_orbitBox_iff n x.1).mpr x.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

end
end StatMech.FrontierD
