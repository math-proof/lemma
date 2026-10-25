/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/IndexOfSpeciality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.RiemannRoch.Part6
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.RiemannRoch
open RiemannRochSpace CurveWithOrd CurveDivisor

variable {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]


/-- A divisor $D$ on a curve is special if its index of speciality $i(D) = \ell(K - D)$ is positive. -/
def IsSpecialDivisor (D : CurveDivisor C) : Prop :=
  0 < indexOfSpeciality (F := F) (k := k) D

