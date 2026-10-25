/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BourgainPerCoord.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.KKLLogOptimisation.Part2
import Def.StatisticalMechanics.Code.Probability.BourgainPerCoord.Part2
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem bph_rhoOptimise_hyp_holds [Nonempty ι] (φ : ConfigSpace ι → Bool) :
    ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
      (∑ S : Finset ι, 4 * (S.card : ℝ) * (ρ ^ (S.card - 1)) ^ 2
          * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
        ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0))
            ^ (2 / (1 + ρ ^ 2) - 1)
          * (∑ S : Finset ι, 4 * (S.card : ℝ)
              * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) :=
  fun _ρ h0 h1 => bph_capped_hc h0 h1 φ


theorem bph_rhoOptimise_zero : bph_RhoOptimise 0 := by
  intro E _ _ _ φ _
  rw [zero_mul, zero_mul]
  exact kls_W_nonneg φ


theorem bph_logOptimisation_of_rho {c : ℝ} (H : bph_RhoOptimise c) :
    kls_LogOptimisation c := by
  intro E _ _ _ φ _hfluct
  exact H φ (fun ρ h0 h1 => bph_capped_hc h0 h1 φ)


theorem bph_KKL {c : ℝ} (H : bph_RhoOptimise c) :
    KKLHypercontractive (1 / 2 : ℝ) c :=
  kls_logSobolevStep (bph_logOptimisation_of_rho H)


end StatMech.Probability
