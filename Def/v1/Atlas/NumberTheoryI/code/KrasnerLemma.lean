/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/KrasnerLemma.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.Analysis.Normed.Field.Krasner
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.FieldTheory.SeparableDegree

@[expose] public section

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
