/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLInequality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Theorem.StatisticalMechanics.Code.OSSS.Poincare.Part2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Def.StatisticalMechanics.Code.Probability.KKLInequality
open scoped BigOperators
open Finset


namespace StatMech

namespace Probability

open StatMech.OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem kkl_totalInfl_nonneg {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (g : ConfigSpace E → ℝ) : 0 ≤ totalInfl ν g :=
  Finset.sum_nonneg (fun e _ => kkl_infl_nonneg hν g e)


end Probability
end StatMech
