/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoherentLimit.Part12
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part5
open Finset SimpleGraph MeasureTheory


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.FK StatMech.FK.PeriodicPlanar

noncomputable section

theorem fkSquarePeriodic_orbitBox_eq_box (n : Nat) :
    square.orbitBox n = (box_finite 2 n).toFinset := by
  ext x
  rw [PeriodicGraph.mem_orbitBox_iff]
  simp [square]

theorem fkSquarePeriodic_mem_orbitBox_iff (n : Nat) (x : Site 2) :
    x ∈ square.orbitBox n ↔ x ∈ box 2 n := by
  rw [PeriodicGraph.mem_orbitBox_iff]
  simp [square]


end
end StatMech.FrontierD
