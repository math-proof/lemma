import Lemma.List.DropPermute__Neg.eq.Cons_TakeDrop.of.GtLength_Add
import Lemma.List.TakeAppend.eq.Take.of.Le_Length
import Lemma.List.TakeCons.eq.Cons_Take
import Lemma.List.TakeTake.eq.Take
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h : s.length > i + d) :
-- imply
  ((s.permute ⟨i + d, h⟩ (-d)).drop i).take (d + 1) = s[i + d] :: (s.drop i).take d := by
-- proof
  rw [DropPermute__Neg.eq.Cons_TakeDrop.of.GtLength_Add h]
  rw [TakeAppend.eq.Take.of.Le_Length]
  ·
    rw [TakeCons.eq.Cons_Take]
    rw [TakeTake.eq.Take]
  ·
    simp
    omega


-- created on 2025-10-29
