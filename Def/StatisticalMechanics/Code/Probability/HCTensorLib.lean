module
public import Theorem.StatisticalMechanics.Code.Probability.PBiasedTensorize.Part11
public import Theorem.StatisticalMechanics.Code.Probability.FullRangeHC.Part2
public import Theorem.StatisticalMechanics.Code.Probability.PBiasedRhoOptimise
public import Theorem.StatisticalMechanics.Code.Probability.VarGapProve2
open scoped BigOperators
open Finset
open Real Set
open StatMech StatMech.OSSS
set_option linter.style.longLine false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HCTensorLib.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def PBiasedHCLib (p : ℝ) : Prop :=
  ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → ∀ u v : ℝ,
    ((1 - p) * u + p * v) ^ 2 + ρ ^ 2 * (p * (1 - p)) * (u - v) ^ 2
      ≤ ((1 - p) * |u| ^ (1 + ρ ^ 2) + p * |v| ^ (1 + ρ ^ 2)) ^ (2 / (1 + ρ ^ 2))


end StatMech.Probability
