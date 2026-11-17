/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

open LinearMap (BilinMap BilinForm)


noncomputable instance instInvertibleTwoOfNeZero (k : Type*) [Field k] [NeZero (2 : k)] :
    Invertible (2 : k) :=
  invertibleOfNonzero (NeZero.ne 2)

