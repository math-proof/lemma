import Lemma.List.EraseIdx.eq.Cons_EraseIdxTail.of.Lt_LengthTail
import Lemma.List.EqEraseIdx.of.Ge_Length
import Lemma.List.EqCons_Tail.of.Eq_Get_0.GtLength_0
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length > 0)
  (i : ℕ) :
-- imply
  s.eraseIdx i.succ = s[0] :: s.tail.eraseIdx i := by
-- proof
  if h_i : i < s.tail.length then
    rw [EraseIdx.eq.Cons_EraseIdxTail.of.Lt_LengthTail h_i s[0]]
    rw [HeadD.eq.Get_0.of.GtLength_0 h]
  else
    simp at h_i
    repeat rw [EqEraseIdx.of.Ge_Length (by simpa using h_i)]
    rw [EqCons_Tail.of.GtLength_0]


-- created on 2025-10-09
