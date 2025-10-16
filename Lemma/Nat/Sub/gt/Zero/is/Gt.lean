import Lemma.Nat.Sub.gt.Zero.is.Lt
open Nat


@[main, comm, mp, mpr]
private lemma main
  [AddCommMonoid α] [LinearOrder α] [CanonicallyOrderedAdd α] [Sub α] [OrderedSub α]
  {a b : α} :
-- imply
  b - a > 0 ↔ b > a :=
-- proof
  Sub.gt.Zero.is.Lt


-- created on 2025-10-16
