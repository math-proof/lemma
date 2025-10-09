import Lemma.List.EraseIdx_Succ.eq.Cons_EraseIdxTail.of.Lt_LengthTail
import Lemma.List.EqEraseIdx.of.Ge_Length
import Lemma.List.EqCons_Tail.of.Eq_Get_0.GtLength_0
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
open List


@[main]
private lemma main
  {v : List α}
-- given
  (h : v.length > 0)
  (i : ℕ) :
-- imply
  v.eraseIdx i.succ = v[0] :: v.tail.eraseIdx i := by
-- proof
  by_cases h_i : i < v.tail.length
  ·
    rw [EraseIdx_Succ.eq.Cons_EraseIdxTail.of.Lt_LengthTail h_i v[0]]
    rw [HeadD.eq.Get_0.of.GtLength_0 h]
  ·
    simp at h_i
    repeat rw [EqEraseIdx.of.Ge_Length (by simpa using h_i)]
    rw [EqCons_Tail.of.GtLength_0]


-- created on 2025-10-09
