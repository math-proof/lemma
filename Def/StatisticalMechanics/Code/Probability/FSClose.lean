/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.EntropySubadditivity.Part2
import Theorem.StatisticalMechanics.Code.Probability.GlobalLSI
import Theorem.StatisticalMechanics.Code.Probability.FSClose
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS


variable {E : Type*} [Fintype E] [DecidableEq E]

def fsc2_EntMassFamily {E : Type} [Fintype E] [DecidableEq E] (p : ℝ) (φ : ConfigSpace E → Bool) : Prop :=
  ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
    esd_ent (OSSS.bernoulliWeight p)
        (fun ω => (ptn_noiseOp p ρ (fun ω => if φ ω then (1 : ℝ) else 0) ω) ^ 2)
      ≤ (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset E,
          (S.card : ℝ) * ((ρ ^ S.card) ^ 2 * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)


end StatMech.Probability
