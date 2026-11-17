/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/AbsoluteValues.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.NumberTheory.Padics.PadicNorm
public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.NumberTheory.Ostrowski
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.FieldTheory.Finite.Basic


@[expose] public noncomputable section

abbrev FieldAbsoluteValue (k : Type*) [Field k] := AbsoluteValue k ℝ

end
