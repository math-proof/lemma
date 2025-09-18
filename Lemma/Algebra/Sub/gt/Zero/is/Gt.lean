import Lemma.Algebra.Sub.gt.Zero.is.Lt
open Algebra


@[main, comm, mp, mpr]
private lemma nat
  [LinearOrderedAddCommMonoid α] [CanonicallyOrderedAdd α] [Sub α] [OrderedSub α]
  {a b : α} :
-- imply
  b - a > 0 ↔ b > a :=
-- proof
  Sub.gt.Zero.is.Lt.nat


/--
This lemma establishes that in an additive group with a strict order and right-strict monotonicity, the difference `b - a` being positive is equivalent to `a` being less than `b`.
It leverages the properties of additive groups and the `AddRightStrictMono` typeclass to connect the algebraic operation of subtraction with the order relation.
-/
@[main, comm, mp, mpr]
private lemma main
  [AddGroup α] [LT α] [AddRightStrictMono α]
  {a b : α} :
-- imply
  b - a > 0 ↔ b > a :=
-- proof
  Sub.gt.Zero.is.Lt


-- created on 2025-08-02
