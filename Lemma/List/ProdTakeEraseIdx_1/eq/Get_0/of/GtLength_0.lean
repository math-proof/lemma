import Lemma.List.TakeEraseIdx.eq.Take.of.Ge
open List


@[main]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h_s : s.length > 0) :
-- imply
  ((s.eraseIdx 1).take 1).prod = s[0] := by
-- proof
  rw [TakeEraseIdx.eq.Take.of.Ge (by omega)]
  aesop


-- created on 2025-11-04
