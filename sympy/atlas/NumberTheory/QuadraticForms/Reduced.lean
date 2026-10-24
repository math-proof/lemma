/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/Reduced.lean -/

import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Gauss-reduced integral binary quadratic forms

This module defines the coefficient-level predicate for Gauss reducedness
following Mortenson, *A Kronecker-type identity* (Bull. LMS 49 (2017)),
author manuscript `arXiv:1702.01627v2`, Section 2, line 259.
-/

namespace BinaryQuadraticForm

/-- Gauss reducedness for the integral binary quadratic form
`a*x^2 + b*x*y + c*y^2` in the strict source convention:

`IsGaussReduced a b c` holds iff `0 < a`, `discrim a b c < 0`,
`|b| ≤ a`, `a ≤ c`, and `(|b| = a ∨ a = c) → 0 ≤ b`.

This is Mortenson `arXiv:1702.01627v2` Section 2 line 259. In particular
`(1,-1,1)` is positive definite and satisfies the loose inequalities but
is not reduced because the tie-break requires `b ≥ 0`. -/
def IsGaussReduced (a b c : ℤ) : Prop :=
  0 < a ∧ discrim a b c < 0 ∧ |b| ≤ a ∧ a ≤ c ∧
    ((|b| = a ∨ a = c) → 0 ≤ b)
end BinaryQuadraticForm
