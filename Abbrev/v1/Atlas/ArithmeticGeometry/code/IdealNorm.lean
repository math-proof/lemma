/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/IdealNorm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.NumberTheory.NumberField.Basic
open Ideal


section IdealNorm

variable {O : Type*} [CommRing O] [Nontrivial O] [IsDedekindDomain O] [Module.Free ℤ O]

noncomputable abbrev idealNorm : Ideal O →*₀ ℕ := Ideal.absNorm


end IdealNorm
