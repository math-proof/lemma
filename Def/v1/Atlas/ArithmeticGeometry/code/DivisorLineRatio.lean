/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/DivisorLineRatio.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.Divisors.Part11
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Divisors
import Structure.v1.Atlas.ArithmeticGeometry.code.DivisorLineRatio


noncomputable section

open CurveDivisor

namespace EllipticCurveP2Data

variable {C : Type*} {F : Type*} [Field F]

noncomputable def pdiv (E : EllipticCurveP2Data C F) (f : Fˣ) : CurveDivisor C :=
  @CurveWithOrd.principalDivisor C F _ E.curveInst f

end EllipticCurveP2Data
end
