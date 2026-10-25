/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TurningTelescope.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWMatrix
import Def.StatisticalMechanics.Code.Onsager.TurningTelescope


namespace StatMech.Onsager

theorem ons_dirStep_opposite (L : ℕ) (μ : Fin 4) (p : ZMod L × ZMod L) :
    ons_dirStep L (μ + 2) (ons_dirStep L μ p) = p := by
  fin_cases μ <;> simp [ons_dirStep]


theorem ons_dartRev_involutive (L : ℕ) : Function.Involutive (ons_dartRev L) := by
  intro d
  obtain ⟨p, μ⟩ := d
  simp only [ons_dartRev]
  rw [Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · exact ons_dirStep_opposite L μ p
  · fin_cases μ <;> decide


theorem ons_dartRev_ne (L : ℕ) [Fact (2 < L)] (d : ons_Dart L) :
    ons_dartRev L d ≠ d := by
  obtain ⟨p, μ⟩ := d
  intro hcontra
  have h2 : (ons_dartRev L (p, μ)).2 = μ := congrArg Prod.snd hcontra
  simp only [ons_dartRev] at h2
  revert h2
  fin_cases μ <;> decide


end StatMech.Onsager
