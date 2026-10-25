/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogOptimisation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.KKLLogSobolev.Part2
import Theorem.StatisticalMechanics.Code.Probability.KKLLogOptimisation
open scoped BigOperators
open Finset
open Real Filter Topology

set_option linter.style.longLine false


namespace StatMech.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def klo_DeltaUpgrade (c : ℝ) : Prop :=
  ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool),
    (∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
        bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)
            - (bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / (1 + ρ ^ 2))
          ≤ (1 - ρ ^ 2) * (∑ S : Finset E, 4 * (S.card : ℝ)
              * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) / 4) →
      c * (∑ S ∈ (univ.erase (∅ : Finset E)),
            (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
          * Real.log (1 / maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ))
              (fun ω => if φ ω then (1 : ℝ) else 0))
        ≤ ∑ S : Finset E, 4 * (S.card : ℝ)
            * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2


end StatMech.Probability
