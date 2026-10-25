/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CriticalIntegrability.Part3
import Theorem.StatisticalMechanics.Code.Onsager.PhaseRegularity.Part11


namespace StatMech.Onsager

noncomputable def ons_freeEnergyIntegralComplex (z : ℂ) : ℂ :=
  (1 / (8 * Real.pi ^ 2) : ℂ) *
    ∫ k1 in (-Real.pi)..Real.pi,
      ∫ k2 in (-Real.pi)..Real.pi,
        Complex.log (ons_gIntComplex z k1 k2)

noncomputable def ons_pressureComplex (z : ℂ) : ℂ :=
  (Real.log 2 : ℂ) + ons_freeEnergyIntegralComplex z

end StatMech.Onsager
