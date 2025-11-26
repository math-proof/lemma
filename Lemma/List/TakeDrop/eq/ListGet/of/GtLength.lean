import Lemma.List.Drop.eq.Cons_Drop_Add_1.of.GtLength
import Lemma.List.TakeCons.eq.List
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h : i < s.length) :
-- imply
  (s.drop i).take 1 = [s[i]] := by
-- proof
  rw [Drop.eq.Cons_Drop_Add_1.of.GtLength (by assumption)]
  rw [TakeCons.eq.List]


-- created on 2025-06-14
