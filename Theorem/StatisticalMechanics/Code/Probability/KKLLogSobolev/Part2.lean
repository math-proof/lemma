/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogSobolev.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.KKLfromHC.Part5
import Def.StatisticalMechanics.Code.Probability.KKLLogSobolev
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem kls_logOptimisation_hyp_holds (φ : ConfigSpace ι → Bool) :
    ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
      (∑ S ∈ (univ.erase (∅ : Finset ι)), (ρ ^ S.card) ^ 2
          * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
        ≤ (bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / (1 + ρ ^ 2))
          - (bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2 :=
  fun _ρ h0 h1 => kls_fluctWeight_le_pow h0 h1 φ


theorem kls_logOptimisation_zero : kls_LogOptimisation 0 := by
  intro E _ _ _ φ _
  rw [zero_mul, zero_mul]
  exact kls_W_nonneg φ


theorem kls_logOptimisation_implies_step {c : ℝ} (H : kls_LogOptimisation c) :
    khc_LogSobolevStep c := by
  intro E _ _ _ φ _hstar
  
  
  
  
  exact H φ (fun ρ h0 h1 => kls_fluctWeight_le_pow h0 h1 φ)


theorem kls_logSobolevStep {c : ℝ} (H : kls_LogOptimisation c) :
    KKLHypercontractive (1 / 2 : ℝ) c :=
  khc_KKL (kls_logOptimisation_implies_step H)


end StatMech.Probability
