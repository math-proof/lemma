import Lemma.List.TakeEraseIdx.eq.Take.of.Ge
open List


@[main]
private lemma main
-- given
  (s : List α) :
-- imply
  (s.eraseIdx i).take i = s.take i := by
-- proof
  apply TakeEraseIdx.eq.Take.of.Ge (by rfl)


-- created on 2025-11-30
