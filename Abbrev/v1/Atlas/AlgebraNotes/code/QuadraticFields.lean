/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/QuadraticFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.RingTheory.DedekindDomain.PID
public import Instance.v1.Atlas.AlgebraNotes.code.QuadraticFields
@[expose] public section

open Polynomial NumberField


noncomputable abbrev QSqrtNeg5 := AdjoinRoot (X ^ 2 + C (5 : ℚ))

