import Lemma.Nat.EqAdd_0
import Lemma.Vector.EqCons_Tail
import Lemma.Vector.Sum.eq.SumVal
import Lemma.Vector.Sum.eq.Zero
open Nat Vector


@[main]
private lemma main
  [AddZeroClass α]
-- given
  (v : List.Vector α 1) :
-- imply
  v.sum = v.head := by
-- proof
  have := Eq_Cons_Tail.head v
  conv_lhs => rw [this]
  simp
  rw [Sum.eq.SumVal]
  simp
  rw [← Sum.eq.SumVal]
  erw [Sum.eq.Zero]
  apply EqAdd_0


-- created on 2026-07-22
