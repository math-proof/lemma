import Lemma.Basic


/--
This lemma asserts the commutativity of the multiplication operation in a commutative magma.
Specifically, for any elements `a` and `b` in the magma, the product `a * b` is equal to `b * a`, as established by the underlying commutative property of the magma's binary operation.
-/
@[main]
private lemma Comm
  [CommMagma α]
-- given
  (a b : α) :
-- imply
  a * b = b * a :=
-- proof
  mul_comm a b


-- created on 2025-06-06
