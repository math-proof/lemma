import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
open List


@[main]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h : s.length > 0) :
-- imply
  (s.eraseIdx 1).prod = s[0] * (s.drop 2).prod := by
-- proof
  rw [EraseIdx.eq.Append_Drop_Add_1]
  simp
  rw [ProdTake_1.eq.Get_0.of.GtLength_0 (by omega)]


-- created on 2025-11-03
