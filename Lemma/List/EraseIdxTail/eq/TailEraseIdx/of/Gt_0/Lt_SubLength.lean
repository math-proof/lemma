import Lemma.List.EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1
open List


@[main, comm]
private lemma main
  {s : List α}
  {i : ℕ}
-- given
  (h_s : s.length > i)
  (h_i : i > 0) :
-- imply
  s.tail.eraseIdx (i - 1) = (s.eraseIdx i).tail := by
-- proof
  rw [EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1]
  .
    apply congrArg
    apply congrArg
    omega
  .
    omega


-- created on 2025-10-09
