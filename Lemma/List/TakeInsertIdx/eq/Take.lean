import Lemma.List.TakeInsertIdx.eq.Take.of.Ge
open List


@[main]
private lemma main
-- given
  (s : List α)
  (x : α) :
-- imply
  (s.insertIdx i x).take i = s.take i := by
-- proof
  apply TakeInsertIdx.eq.Take.of.Ge (by rfl)


-- created on 2025-11-30
