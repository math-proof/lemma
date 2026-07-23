import Lemma.Nat.EqAdd0
import Lemma.Vector.EqCons_Tail
import Lemma.Vector.EqGet0_0
import Lemma.Vector.Head.eq.Get_0
import Lemma.Vector.SumCons.eq.Add_Sum
open Nat Vector


@[main]
private lemma main
  [AddZeroClass α]
-- given
  (n : ℕ) :
-- imply
  (0 : List.Vector α n).sum = 0 := by
-- proof
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    erw [Eq_Cons_Tail.head (0 : List.Vector α (n + 1))]
    erw [SumCons.eq.Add_Sum]
    rw [Head.eq.Get_0.fin]
    rw [EqGet0_0.fin]
    erw [ih]
    apply EqAdd0


-- created on 2026-07-23
