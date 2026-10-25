/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.EntropySubadditivity.Part2
import Theorem.StatisticalMechanics.Code.Probability.GlobalLSI
import Theorem.StatisticalMechanics.Code.Probability.FSClose.Part2
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS


variable {E : Type*} [Fintype E] [DecidableEq E]

def fsc2_DampingHardResidue (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, p < 1 → ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (φ : ConfigSpace E → Bool),
    0 < OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) →
      0 < maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) →
      maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        < Real.exp (-(1 / (2 * (p * (1 - p))))) →
      fsc2_EntMassFamily p φ →
        pen_dampedMass p (Real.exp (-(1 / (2 * (p * (1 - p)))))) (fun ω => if φ ω then (1 : ℝ) else 0)
          ≤ maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
            * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)


end StatMech.Probability
