import sympy.Basic


/--
This lemma asserts the commutativity of the addition operation in an additive commutative magma (`AddCommMagma`).
It demonstrates that for any two elements `a` and `b` in the magma, the sum `a + b` is equal to `b + a`, a property inherent to the structure's algebraic definition.
-/
@[main]
private lemma Comm
  [AddCommMagma α]
  {a b : α} :
-- imply
  a + b = b + a := by
-- proof
  apply add_comm


-- created on 2024-07-01
-- updated on 2025-04-04
