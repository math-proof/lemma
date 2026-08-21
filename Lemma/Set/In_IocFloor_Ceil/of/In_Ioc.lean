import sympy.sets.sets
import Lemma.Algebra.Le_Ceil
import Lemma.Rat.LeFloor
open Algebra Rat


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {a b x : α}
-- given
  (h : x ∈ Ioc a b) :
-- imply
  x ∈ Ioc (⌊a⌋ : α) (⌈b⌉ : α) := by
-- proof
  constructor
  ·
    exact lt_of_le_of_lt (LeFloor a) h.1
  ·
    exact le_trans h.2 (Le_Ceil (x := b))


-- created on 2018-08-29
-- updated on 2026-08-20
