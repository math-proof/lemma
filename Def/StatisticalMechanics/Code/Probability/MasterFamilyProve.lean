/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.VarGapProve2
import Theorem.StatisticalMechanics.Code.Probability.PBiasedTwoPoint.Part3
import Theorem.StatisticalMechanics.Code.Probability.MasterFamilyProve
open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def mfp_SingleBitQGt2 (p : ℝ) : Prop :=
  ∀ u : ℝ, 0 < u → u < 1 → ∀ u₀ v₀ : ℝ,
    ((1 - p) * u₀ + p * v₀) ^ 2 + (1 - u) * (p * (1 - p)) * (u₀ - v₀) ^ 2
      ≤ ((1 - p) * |u₀| ^ (2 - u) + p * |v₀| ^ (2 - u)) ^ (2 / (2 - u))


end StatMech.Probability
