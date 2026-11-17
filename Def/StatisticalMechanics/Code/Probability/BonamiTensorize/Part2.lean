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
public import Theorem.StatisticalMechanics.Code.Probability.BonamiTensorize

@[expose] public section

open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


noncomputable def bnt_noiseKernel (ρ : ℝ) (x y : ι → Bool) : ℝ :=
  ∏ i : ι, (if x i = y i then (1 + ρ) / 2 else (1 - ρ) / 2)


noncomputable def bnt_noiseOp (ρ : ℝ) (f : (ι → Bool) → ℝ) : (ι → Bool) → ℝ :=
  fun x => ∑ y : ι → Bool, bnt_noiseKernel ρ x y * f y


end Probability
end StatMech
