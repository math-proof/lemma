/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/EffectiveParts.lean -/

import sympy.atlas.AlgebraicGeometry.Curve.Divisor
import Lemma.Finsupp.EqCoeff_Single
import Mathlib.Data.Finsupp.Order
import Mathlib.Algebra.Order.Group.PosPart

/-!
# Effective parts of curve divisors

This file separates a divisor into its effective zero and pole parts.
-/

namespace CurveDivisor

variable {C : Type*}

/-- The effective zero part of a divisor. -/
noncomputable def divZeros (D : CurveDivisor C) : CurveDivisor C :=
  D⁺

/-- The effective pole part of a divisor. -/
noncomputable def divPoles (D : CurveDivisor C) : CurveDivisor C :=
  D⁻
end CurveDivisor
