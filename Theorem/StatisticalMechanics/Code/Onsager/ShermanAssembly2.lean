/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanAssembly2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWLoopWeight
import Theorem.StatisticalMechanics.Code.Onsager.ShermanAssembly1


namespace StatMech.Onsager

open Matrix BigOperators Finset


theorem ons_turnW_omega_inv (ω : ℂ) (μ ν : Fin 4) :
    ons_turnW ω⁻¹ μ ν = (ons_turnW ω μ ν)⁻¹ := by
  unfold ons_turnW
  split_ifs <;> simp


theorem ons_KWmat_dartRev (L : ℕ) (x ω : ℂ) (d₁ d₂ : ons_Dart L) :
    ons_KWmat L x ω (ons_dartRev L d₁) (ons_dartRev L d₂)
      = ons_KWmat L x ω⁻¹ d₂ d₁ := by
  obtain ⟨p₁, μ₁⟩ := d₁
  obtain ⟨p₂, μ₂⟩ := d₂
  simp only [ons_KWmat, ons_dartRev, ons_dirStep_opposite]
  rw [ons_turnW_rev ω μ₁ μ₂, ons_turnW_omega_inv]
  by_cases h : ons_dirStep L μ₁ p₁ = p₂
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hc => h hc.symm)]


end StatMech.Onsager
