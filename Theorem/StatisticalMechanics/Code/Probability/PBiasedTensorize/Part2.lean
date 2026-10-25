/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.PBiasedConvexity.Part2
import Theorem.StatisticalMechanics.Code.Probability.KKLpBiased.Part2
import Theorem.StatisticalMechanics.Code.Probability.RhoOptimiseClose2
import Def.StatisticalMechanics.Code.Probability.PBiasedTensorize.Part2
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem ptn_sigma_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 < ptn_sigma p :=
  Real.sqrt_pos.mpr (by nlinarith)

theorem ptn_sigma_sq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ptn_sigma p ^ 2 = p * (1 - p) := by
  unfold ptn_sigma; rw [Real.sq_sqrt (by nlinarith)]


end StatMech.Probability
