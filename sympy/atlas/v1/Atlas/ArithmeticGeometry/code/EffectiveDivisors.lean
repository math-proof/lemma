/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EffectiveDivisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.Divisors
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Divisors

namespace CurveDivisor

variable {C : Type*}

def IsEffective (D : CurveDivisor C) : Prop := ∀ P, 0 ≤ D P


noncomputable def positivePart (D : CurveDivisor C) : CurveDivisor C :=
  Finsupp.mapRange (fun n => max n 0) (by simp) D

noncomputable def negativePart (D : CurveDivisor C) : CurveDivisor C :=
  Finsupp.mapRange (fun n => max (-n) 0) (by simp) D
