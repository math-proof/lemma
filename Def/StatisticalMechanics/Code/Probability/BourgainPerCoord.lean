/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BourgainPerCoord.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.KKLLogOptimisation.Part2
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


noncomputable def bph_deriv (f : ConfigSpace ι → ℝ) (e : ι) : ConfigSpace ι → ℝ :=
  fun ω => f (StatMech.setOpen e ω) - f (StatMech.setClosed e ω)


end StatMech.Probability
