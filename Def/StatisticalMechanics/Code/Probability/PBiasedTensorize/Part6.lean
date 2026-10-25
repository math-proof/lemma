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
import Theorem.StatisticalMechanics.Code.Probability.PBiasedTensorize.Part5
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


noncomputable def ptn_qnormPow (p q : ℝ) (f : ConfigSpace ι → ℝ) : ℝ :=
  OSSS.expect (OSSS.bernoulliWeight p) (fun ω => |f ω| ^ q)


noncomputable def ptn_qnorm (p q : ℝ) (f : ConfigSpace ι → ℝ) : ℝ :=
  (ptn_qnormPow p q f) ^ (1 / q)

end StatMech.Probability
