import Lemma.Vector.SumCons.eq.Add_Sum
import Lemma.Vector.EqCons_Tail
import Lemma.Vector.Sum.eq.Zero
import Lemma.Vector.EqHeadD
import Lemma.Vector.EqHeadDCons
open Vector


@[main]
private lemma main
  [AddMonoid α]
  (v : List.Vector α n) :
-- imply
  v.sum = (v.headD 0) + v.tail.sum := by
-- proof
  match n with
  | 0 =>
    simp [EqHeadD, Sum.eq.Zero]
  | n + 1 =>
    rw [Eq_Cons_Tail v]
    simp [SumCons.eq.Add_Sum, EqHeadDCons]


-- created on 2024-07-01
-- updated on 2025-10-03
