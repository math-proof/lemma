/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAntiperiodicSectorLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingUniformMode.Part5
import Theorem.StatisticalMechanics.Code.Onsager.RiemannPeriodicVarying
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAntiperiodicSectorLimit
open scoped BigOperators
open Filter


namespace StatMech.FrontierA

open StatMech.Onsager

noncomputable def quantumIsingZeroOneSectorLogDensity
    (beta h : Real) (n : Nat) : Real := by
  letI : Fact (2 < n + 3) := ⟨by omega⟩
  exact (2 * Real.log
    ‖quantumIsingNormalizedSpinSector beta h (n + 3) 0 1‖) / (n + 3)

end StatMech.FrontierA
