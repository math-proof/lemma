import Lemma.Int.SubSub
import Lemma.List.Permute__Neg.eq.Append_AppendRotateDropTake
import Lemma.List.TailAppend.eq.AppendTail.of.GtLength_0
import Lemma.List.TailTake.eq.TakeTail
import Lemma.List.TailTake.eq.TakeTail.of.Gt_0
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqMin.of.Le
open Int List Nat


@[main]
private lemma main
  {s : List α}
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h_d : i > d) :
-- imply
  (s.permute i (-d)).tail = s.tail.permute ⟨i - 1, by grind⟩ (-d) := by
-- proof
  simp [Permute__Neg.eq.Append_AppendRotateDropTake]
  repeat rw [EqMin.of.Le (by omega)]
  rw [EqAddSub.of.Ge (by omega)]
  rw [TailAppend.eq.AppendTail.of.GtLength_0 (by simp; omega)]
  rw [TailTake.eq.TakeTail.of.Gt_0 (by omega)]
  rw [TailTake.eq.TakeTail]
  simp [SubSub.comm]
  simp [← TailTake.eq.TakeTail]
  rw [EqAddSub.of.Ge (by omega)]


-- created on 2025-12-03
