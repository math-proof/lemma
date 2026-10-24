/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRochP1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.RiemannRoch
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.RiemannRoch
import Mathlib.FieldTheory.RatFunc.Basic

open RiemannRochSpace CurveDivisor CurveWithOrd

namespace RiemannRochSpace

variable {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]

/-- A rational curve (function field $\cong k(t)$) has trivial $\mathrm{Pic}^0$ (every degree-$0$ divisor is principal) and infinitely many points. -/
def HasPrescribedPoles (f : Fˣ) (A : CurveDivisor C) : Prop :=
  (principalDivisor (C := C) f + A).IsEffective ∧
  ∀ P : C, A P > 0 → CurveWithOrd.ord (F := F) P f = -(A P)
