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
public import Theorem.StatisticalMechanics.Code.Probability.BonamiTensorize.Part3

@[expose] public section

open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def bnt_TensorStep (ρ : ℝ) : Prop :=
  ∀ n : ℕ,
    (∀ g : (Fin n → Bool) → ℝ, bnt_qnorm 2 (bnt_noiseOp ρ g) ≤ bnt_qnorm (1 + ρ ^ 2) g) →
    (∀ f : (Fin (n + 1) → Bool) → ℝ,
      bnt_qnorm 2 (bnt_noiseOp ρ f) ≤ bnt_qnorm (1 + ρ ^ 2) f)


end Probability
end StatMech
