/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RegularObject.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section


/-- A formal real-coefficient combination of objects indexed by `I`, used to
represent formal sums of projective covers in the Grothendieck setting. -/
abbrev FormalProjectiveSum (I : Type*) := I →₀ ℝ

