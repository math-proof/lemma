import sympy.core.power
import Lemma.Basic


/--
This lemma establishes the algebraic identity for the difference of cubes, demonstrating that \( x^3 - y^3 \) factors into \( (x - y)(x^2 + xy + y^2) \).
Verified within the context of a field \( \alpha \), it confirms the validity of this factorization across various mathematical structures where field operations are defined.
-/
@[main]
private lemma main
  [CommRing α]
  {x : α} :
-- imply
  x³ - y³ = (x - y) * (x² + y² + x * y) := by
-- proof
  ring


-- created on 2025-03-24
-- updated on 2025-04-04
