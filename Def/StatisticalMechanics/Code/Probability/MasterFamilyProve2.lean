/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.MasterFamilyProve.Part3
import Theorem.StatisticalMechanics.Code.Probability.MasterFamilyProve2
open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def mfp2_PerCoordHighNoise (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, p < 1 → ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (φ : ConfigSpace E → Bool), ∀ u : ℝ, 0 < u → u < 1 → ∀ e : E,
      (∑ S ∈ univ.filter (fun S : Finset E => e ∈ S),
          (1 - u) ^ (S.erase e).card * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S
            / ptn_sigma p) ^ 2)
        ≤ (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / (2 - u))


end StatMech.Probability
