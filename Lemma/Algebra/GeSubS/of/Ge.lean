import Lemma.Algebra.LeSubS.is.Le
import Lemma.Algebra.LeSubS.of.Le
open Algebra


@[main]
private lemma nat
  {x y : ℕ}
-- given
  (h : x ≥ y)
  (z : ℕ) :
-- imply
  x - z ≥ y - z := by
-- proof
  apply LeSubS.of.Le.nat h


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {x y : α}
-- given
  (h : x ≥ y)
  (z : α) :
-- imply
  x - z ≥ y - z :=
-- proof
  LeSubS.of.Le z h


-- created on 2024-07-01
-- updated on 2025-03-31
