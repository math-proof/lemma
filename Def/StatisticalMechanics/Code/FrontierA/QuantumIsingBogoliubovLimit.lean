/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBogoliubovLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.RiemannPeriodic
open scoped BigOperators
open MeasureTheory


namespace StatMech.FrontierA

noncomputable def quantumIsingDispersion (h k : ℝ) : ℝ :=
  Real.sqrt (1 + 4 * h ^ 2 + 4 * h * Real.cos k)


noncomputable def quantumIsingModeLog (beta h k : ℝ) : ℝ :=
  Real.log (Real.cosh (beta / 4 * quantumIsingDispersion h k))


noncomputable def quantumIsingFreeEnergyValue (beta h : ℝ) : ℝ :=
  -Real.log 2 / beta -
    (1 / (2 * Real.pi * beta)) *
      ∫ k in (-Real.pi)..Real.pi, quantumIsingModeLog beta h k


noncomputable def quantumIsingBogoliubovFreeEnergy
    (beta h : ℝ) (L : ℕ) : ℝ :=
  -Real.log 2 / beta -
    (1 / (beta * L)) *
      ∑ j ∈ Finset.range L,
        quantumIsingModeLog beta h (2 * Real.pi * j / L)

end StatMech.FrontierA
