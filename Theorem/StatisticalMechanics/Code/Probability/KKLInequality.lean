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
open scoped BigOperators
open Finset


namespace StatMech

namespace Probability

open StatMech.OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem kkl_infl_nonneg {ν : E → Bool → ℝ} (hν : IsProbWeight ν) (g : ConfigSpace E → ℝ)
    (e : E) : 0 ≤ OSSS.infl ν g e := by
  unfold OSSS.infl OSSS.expect
  apply Finset.sum_nonneg
  intro ω _
  have hw : 0 ≤ OSSS.weight ν ω :=
    Finset.prod_nonneg (fun e _ => hν.nonneg e (ω e))
  positivity


end Probability
end StatMech
