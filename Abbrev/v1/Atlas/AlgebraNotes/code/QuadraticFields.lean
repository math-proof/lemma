/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/QuadraticFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.DedekindDomain.PID
import Instance.v1.Atlas.AlgebraNotes.code.QuadraticFields
open Polynomial NumberField


noncomputable abbrev QSqrtNeg5 := AdjoinRoot (X ^ 2 + C (5 : ℚ))

