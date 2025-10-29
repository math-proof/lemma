import Lemma.List.GetDrop.eq.Get_Add.of.GtLength_Add
import Lemma.List.Take.eq.AppendTake.of.Lt_Length
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h : i + d < s.length) :
-- imply
  (s.drop i).take (d + 1) = (s.drop i).take d ++ [s[i + d]] := by
-- proof
  rw [Take.eq.AppendTake.of.Lt_Length (s := s.drop i)]
  ·
    rw [GetDrop.eq.Get_Add.of.GtLength_Add]
  ·
    simp
    omega


-- created on 2025-10-29
