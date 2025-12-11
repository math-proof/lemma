import Lemma.Int.Mul.gt.Zero.is.AndGtS_0.ou.AndLtS_0
import Lemma.Rat.Div.gt.Zero.is.AndGtS_0.ou.AndLtS_0
open Rat Int


@[main, comm, mp, mpr]
private lemma main
  [Field α]
  [LinearOrder α]
  [IsStrictOrderedRing α]
-- given
  (a b : α) :
-- imply
  a / b > 0 ↔ a * b > 0 := by
-- proof
  rw [Div.gt.Zero.is.AndGtS_0.ou.AndLtS_0]
  rw [← Mul.gt.Zero.is.AndGtS_0.ou.AndLtS_0]


-- created on 2025-12-11
