/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PicardGroup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.Divisors.Part11
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Divisors


namespace Theorem19_14

variable (C : Type*) (k : Type*) (F : Type*) [Field k] [Field F]
  [Algebra k F] [inst : CurveWithConstants C k F]

open CurveWithOrd CurveWithConstants

noncomputable def divMap : Fˣ → CurveDivisor C :=
  fun f => principalDivisor (C := C) f

noncomputable def toPicMap :
    CurveDivisor C →+ CurveDivisor C ⧸ principalDivisors (C := C) (F := F) :=
  QuotientAddGroup.mk' principalDivisors

end Theorem19_14
