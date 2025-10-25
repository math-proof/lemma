import sympy.core.power
import sympy.Basic


/--
This lemma confirms that in a monoid, the square of an element `x` is defined as the product of `x` with itself.
It ensures the consistency of exponentiation with the monoid's multiplicative structure, serving as a basic yet essential property in algebraic manipulations.
-/
@[main, comm]
private lemma main
  [Monoid α]
-- given
  (x : α) :
-- imply
  x² = x * x :=
-- proof
  pow_two x


-- created on 2024-07-01
-- updated on 2025-04-04
