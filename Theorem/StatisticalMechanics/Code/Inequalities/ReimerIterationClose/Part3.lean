/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerIterationClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve3.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompressLib.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve2.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerEndpointProve.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
import Def.StatisticalMechanics.Code.Inequalities.ReimerIterationClose.Part2
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rit_familyEvent_eventFamily (A : Set (ConfigSpace α)) :
    familyEvent (eventFamily A) = A := by
  classical
  ext ω
  simp only [mem_familyEvent, eventFamily, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨ω', hω', heq⟩
    have hωeq : ω' = ω := by
      have := congrArg supportCfg heq
      rwa [supportCfg_cfgSupport, supportCfg_cfgSupport] at this
    rwa [hωeq] at hω'
  · intro hω; exact ⟨ω, hω, rfl⟩


theorem rit_fmarg_symm_iterDownComp {w : α → Bool → ℝ} (hsym : ∀ x, w x false = w x true)
    (cs : List α) (𝒜 : Finset (Finset α)) :
    fmarg w (iterDownComp cs 𝒜) = fmarg w 𝒜 := by
  induction cs with
  | nil => rfl
  | cons i cs ih => rw [iterDownComp_cons, fmarg_symm_downComp hsym, ih]


end StatMech
