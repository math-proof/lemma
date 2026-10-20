/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/EffectiveParts.lean -/

import sympy.atlas.AlgebraicGeometry.Curve.Divisor
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

/-- The coefficient of the zero part is the positive part of the coefficient. -/
@[simp]
theorem divZeros_apply (D : CurveDivisor C) (P : C) :
    divZeros D P = max (D P) 0 :=
  rfl

/-- The coefficient of the pole part is the negative part of the coefficient. -/
@[simp]
theorem divPoles_apply (D : CurveDivisor C) (P : C) :
    divPoles D P = max (-(D P)) 0 :=
  rfl

/-- The zero part of a divisor is effective. -/
@[simp]
theorem divZeros_nonneg (D : CurveDivisor C) : 0 ≤ divZeros D :=
  posPart_nonneg D

/-- The pole part of a divisor is effective. -/
@[simp]
theorem divPoles_nonneg (D : CurveDivisor C) : 0 ≤ divPoles D :=
  negPart_nonneg D

/-- Subtracting the pole part from the zero part recovers the divisor. -/
@[simp]
theorem divZeros_sub_divPoles (D : CurveDivisor C) :
    divZeros D - divPoles D = D := by
  ext P
  exact posPart_sub_negPart (D P)

end CurveDivisor
