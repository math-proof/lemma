import Lemma.List.Drop.eq.Nil.of.LeLength
import Lemma.List.EqEraseIdx.of.LeLength
import Lemma.List.EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1
import Lemma.List.EraseIdx_0.eq.Tail
import Lemma.List.Tail.eq.Nil.of.LeLength_1
import Lemma.List.TailTail.eq.Drop_2
open List


@[main]
private lemma main
-- given
  (s : List α) :
-- imply
  (s.eraseIdx 1).tail = s.drop 2 := by
-- proof
  if h : s.length > 1 then
    rw [← EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1]
    ·
      rw [EraseIdx_0.eq.Tail]
      rw [TailTail.eq.Drop_2]
    ·
      omega
  else
    rw [EqEraseIdx.of.LeLength (by omega)]
    rw [Drop.eq.Nil.of.LeLength (by omega)]
    rw [Tail.eq.Nil.of.LeLength_1 (by omega)]


-- created on 2025-11-04
