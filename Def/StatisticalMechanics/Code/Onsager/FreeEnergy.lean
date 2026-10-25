/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/FreeEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.Pressure.Part2
import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Theorem.StatisticalMechanics.Code.Onsager.CriticalPoint


namespace StatMech.Onsager

open StatMech.Ising


noncomputable def ons_freeEnergyIntegral (β : ℝ) : ℝ :=
  (1 / (8 * Real.pi ^ 2)) *
    ∫ k₁ in (-Real.pi)..Real.pi, ∫ k₂ in (-Real.pi)..Real.pi, Real.log (ons_gInt β k₁ k₂)


noncomputable def ons_pressure (β : ℝ) : ℝ := Real.log 2 + ons_freeEnergyIntegral β


def ons_KacWardResidue (β : ℝ) : Prop :=
  Filter.Tendsto
    (fun L : ℕ => if h : 2 < L then
        (letI : Fact (2 < L) := ⟨h⟩
         Real.log (ons_X (onsTorusGraph L) (Real.tanh β)) / ((L : ℝ) ^ 2))
      else 0)
    Filter.atTop
    (nhds (ons_freeEnergyIntegral β - 2 * Real.log (Real.cosh β)))


end StatMech.Onsager
