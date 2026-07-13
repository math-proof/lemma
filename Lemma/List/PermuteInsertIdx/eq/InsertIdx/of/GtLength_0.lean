import Lemma.List.InsertIdx_Length.eq.Append_List
import Lemma.List.InsertIdx.eq.Append_Cons.of.GeLength
import Lemma.List.Permute.eq.Ite
import Lemma.List.TakeAppend.eq.Take.of.GeLength
import Lemma.List.Drop_SubLength_1.eq.ListGet.of.GtLength_0
import Lemma.List.GetAppend.eq.Get_Sub_Length.of.GtLengthAppend.GeLength
import Lemma.List.SliceTake.eq.Slice.of.Ge
import Lemma.List.Slice.eq.DropTake
import Lemma.List.EqTake
import Lemma.List.Drop.eq.Nil.of.LeLength
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h_s : s.length > 0)
  (a : α) :
-- imply
  (s.insertIdx s.length a).permute ⟨s.length, by simp⟩ (-1) = s.insertIdx (s.length - 1) a := by
-- proof
  suffices h : (s ++ [a]).permute ⟨s.length, by simp⟩ (-1) = s.insertIdx (s.length - 1) a by
    have := InsertIdx_Length.eq.Append_List s a
    grind
  rw [InsertIdx.eq.Append_Cons.of.GeLength (by omega)]
  rw [Permute.eq.Ite]
  simp only [if_pos (show (-1 : ℤ) < 0 by decide)]
  simp only [show (-(-1 : ℤ)).toNat = 1 by simp]
  rw [TakeAppend.eq.Take.of.GeLength (by omega)]
  have hi : s.length < (s ++ [a]).length := by simp
  have h_get : (s ++ [a])[s.length] = a := by
    rw [GetAppend.eq.Get_Sub_Length.of.GtLengthAppend.GeLength (by omega) (by simp)]
    simp
  conv_lhs =>
    pattern (s ++ [a])[_]
    simp [h_get]
  rw [Drop.eq.Nil.of.LeLength (s := s ++ [a]) (i := s.length + 1) (by simp)]
  rw [← SliceTake.eq.Slice.of.Ge (s := s ++ [a]) (i := s.length - 1) (j := s.length) (j' := s.length) (by omega)]
  rw [TakeAppend.eq.Take.of.GeLength (a := s) (b := [a]) (i := s.length) (by omega), EqTake, Slice.eq.DropTake, EqTake, Drop_SubLength_1.eq.ListGet.of.GtLength_0 h_s]
  simp


-- created on 2026-07-11
