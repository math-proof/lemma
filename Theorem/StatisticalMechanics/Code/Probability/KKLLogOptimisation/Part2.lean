/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogOptimisation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.KKLLogSobolev.Part2
import Def.StatisticalMechanics.Code.Probability.KKLLogOptimisation
open scoped BigOperators
open Finset
open Real Filter Topology

set_option linter.style.longLine false


namespace StatMech.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem klo_deltaUpgrade_hyp_holds (φ : ConfigSpace ι → Bool) :
    ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
      bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)
          - (bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / (1 + ρ ^ 2))
        ≤ (1 - ρ ^ 2) * (∑ S : Finset ι, 4 * (S.card : ℝ)
            * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) / 4 :=
  fun ρ h0 h1 => klo_master_le φ ρ h0 h1


theorem klo_deltaUpgrade_zero : klo_DeltaUpgrade 0 := by
  intro E _ _ _ φ _
  rw [zero_mul, zero_mul]
  exact kls_W_nonneg φ


theorem klo_logOptimisation_of_deltaUpgrade {c : ℝ} (H : klo_DeltaUpgrade c) :
    kls_LogOptimisation c := by
  intro E _ _ _ φ _hfluct
  
  
  
  exact H φ (fun ρ h0 h1 => klo_master_le φ ρ h0 h1)


theorem klo_logOptimisation {c : ℝ} (H : klo_DeltaUpgrade c) :
    KKLHypercontractive (1 / 2 : ℝ) c :=
  kls_logSobolevStep (klo_logOptimisation_of_deltaUpgrade H)


end StatMech.Probability
