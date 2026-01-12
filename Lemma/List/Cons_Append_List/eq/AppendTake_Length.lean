import Lemma.List.AppendAppend.eq.Append_Append
import Lemma.List.Cons.eq.Append
import Lemma.List.GetAppend.eq.Get.of.GtLength
import Lemma.List.GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0
import Lemma.List.Ne_Nil.is.GtLength_0
import Lemma.List.TakeAppend.eq.Take.of.GeLength
import Lemma.List.TakeCons.eq.Cons_Take.of.Gt_0
open List


@[main, comm]
private lemma main
-- given
  (s : List α)
  (a n k : α) :
-- imply
  a :: (s ++ [n]) = (a :: (s ++ [k])).take s.length ++ [(a :: (s ++ [k]))[s.length], n] := by
-- proof
  if h : s = [] then
    simp [h]
  else
    have h := GtLength_0.of.Ne_Nil h
    rw [GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0 h (by simp; omega)]
    rw [GetAppend.eq.Get.of.GtLength (by simpa)]
    simp [TakeCons.eq.Cons_Take.of.Gt_0 h]
    rw [TakeAppend.eq.Take.of.GeLength (by simp)]
    conv_rhs => rw [Cons.eq.Append]
    rw [Append_Append.eq.AppendAppend]
    simp
    omega


-- created on 2026-01-12
