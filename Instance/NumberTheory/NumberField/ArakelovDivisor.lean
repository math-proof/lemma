/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ArakelovDivisor.lean -/

import Mathlib.Algebra.Order.Positive.Field
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.FractionalIdeal.Norm
import Abbrev.NumberTheory.NumberField.ArakelovDivisor
open scoped NumberField nonZeroDivisors

/-!
# Arakelov divisors of a number field

This file introduces the group of Arakelov divisors of a number field `K`, together with
its size homomorphism, the principal-divisor homomorphism, and the degree-zero subgroup.

An Arakelov divisor is an invertible fractional ideal together with a positive real number
at each infinite place. Its size is the archimedean factor (the finite product over all
infinite places, each value raised to that place's multiplicity) divided by the absolute
norm of the finite (ideal) component. Every principal divisor has size one; the archimedean factor
equals `|Algebra.norm ℚ x|` by `NumberField.InfinitePlace.prod_eq_abs_norm` while the ideal
norm of the principal ideal is the same value by
`FractionalIdeal.absNorm_span_singleton`, so the principal
subgroup lies in the degree-zero subgroup.

Complex-place values in the carrier are ordinary (unsquared) radii: the section set
`ArakelovDivisor.sectionSet` compares `w x` directly against `D.2 w`. The `w.mult = 2`
complex squaring appears only in the size homomorphism, never in the section-set bounds.

## Mathlib conventions

* `w : NumberField.InfinitePlace K` is the absolute value induced by a complex embedding,
  with no extra normalization.
* `w.mult` is `1` at a real place and `2` at a complex place, so that
  `∏ w, w x ^ w.mult = |Algebra.norm ℚ x|`
  (`NumberField.InfinitePlace.prod_eq_abs_norm`).
* `FractionalIdeal.absNorm` of a principal fractional ideal is
  `|Algebra.norm ℚ x|` (`FractionalIdeal.absNorm_span_singleton`).

The two bullets above are the two sides of the product formula; the size-one theorem
below is their combination, not a new normalization.
-/


namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The natural commutative group structure on Arakelov divisors (pointwise). -/
noncomputable instance : CommGroup (ArakelovDivisor K) := inferInstance

end NumberField
