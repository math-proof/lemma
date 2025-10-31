import Lemma.Vector.SumCons.eq.Add_Sum
import Lemma.Vector.Sum.eq.Zero
import Lemma.Vector.EqHeadD
import Lemma.Vector.EqHeadDCons
open Vector


@[main]
private lemma main
  [AddMonoid α]
  {l : List.Vector α n} :
-- imply
  l.sum = (l.headD 0) + l.tail.sum := by
-- proof
  match n with
  | 0 =>
    simp [EqHeadD, Sum.eq.Zero]
  | n + 1 =>
    have h : l = l.head ::ᵥ l.tail := by simp
    rw [h]
    rw [
      SumCons.eq.Add_Sum l.head l.tail,
      EqHeadDCons
    ]
    simp


-- created on 2024-07-01
-- updated on 2025-10-03
