/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Height/Absolute.lean -/

import Mathlib.NumberTheory.Height.NumberField

/-!
# Absolute heights of algebraic numbers

This file supplements Mathlib's absolute-height definitions with elementary bounds and a primitive
integral representative of the rational minimal polynomial.
-/

namespace NumberField

open IntermediateField Polynomial

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- A primitive integral normalization of the rational minimal polynomial of `x`.

For algebraic `x`, this is a primitive integral representative of `minpoly ℚ x`. For
nonalgebraic `x`, Mathlib defines `minpoly ℚ x` to be zero, and `primPart` consequently gives its
conventional fallback value `1`. The sign is immaterial for applications to Mahler measure. -/
noncomputable def primitiveIntMinpoly (x : K) : ℤ[X] :=
  (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ x)).primPart
end NumberField
