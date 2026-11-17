/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Def.StatisticalMechanics.Code.Probability.BonamiTensorize
open scoped BigOperators
open Finset

set_option linter.style.longLine false

public section

namespace StatMech

namespace Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem bnt_qnormPow_nonneg (q : ℝ) (f : (ι → Bool) → ℝ) : 0 ≤ bnt_qnormPow q f := by
  unfold bnt_qnormPow bnt_uexp
  apply div_nonneg
  · exact Finset.sum_nonneg (fun ω _ => Real.rpow_nonneg (abs_nonneg _) q)
  · positivity


theorem bnt_qnorm_nonneg (q : ℝ) (f : (ι → Bool) → ℝ) : 0 ≤ bnt_qnorm q f :=
  Real.rpow_nonneg (bnt_qnormPow_nonneg q f) _


end Probability
end StatMech
