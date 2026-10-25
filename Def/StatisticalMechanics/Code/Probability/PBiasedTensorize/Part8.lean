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
import Theorem.StatisticalMechanics.Code.Probability.PBiasedTensorize.Part7
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


noncomputable def ptn_kbit (p ρ : ℝ) (x y : Bool) : ℝ :=
  ρ * (if x = y then 1 else 0) + (1 - ρ) * (if y then p else 1 - p)


noncomputable def ptn_kernel (p ρ : ℝ) (x y : ConfigSpace ι) : ℝ :=
  ∏ i : ι, ptn_kbit p ρ (x i) (y i)


noncomputable def ptn_kop (p ρ : ℝ) (f : ConfigSpace ι → ℝ) : ConfigSpace ι → ℝ :=
  fun x => ∑ y : ConfigSpace ι, ptn_kernel p ρ x y * f y


end StatMech.Probability
