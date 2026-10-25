/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/KrasnerLemma.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.Normed.Field.Krasner
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.SeparableDegree
open Polynomial Finset


noncomputable def Polynomial.L1norm {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (f : Polynomial K) : ℝ :=
  f.support.sum (fun i => v (f.coeff i))

namespace Polynomial

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (f : Polynomial K)

def BelongsTo (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (β α : AlgebraicClosure K) : Prop :=
  ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
    σ α ≠ α →
    spectralNorm K (AlgebraicClosure K) (β - α) <
      spectralNorm K (AlgebraicClosure K) (β - σ α)

noncomputable def normAbsVal (K : Type*) [NormedField K] : AbsoluteValue K ℝ where
  toFun k := ‖k‖
  map_mul' := norm_mul
  nonneg' := norm_nonneg
  eq_zero' := by simp [norm_eq_zero]
  add_le' := norm_add_le

end Polynomial
