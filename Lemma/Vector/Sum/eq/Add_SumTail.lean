import Lemma.Vector.SumCons.eq.Add_Sum
import Lemma.Vector.EqCons_Tail
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
    rw [← EqCons_Tail l]
    have h_add := SumCons.eq.Add_Sum l.head l.tail
    have h_head:= EqHeadDCons l l.head 0
    simp at h_head
    conv_rhs at h_add => rw [← h_head]
    simpa


-- created on 2024-07-01
-- updated on 2025-10-03
