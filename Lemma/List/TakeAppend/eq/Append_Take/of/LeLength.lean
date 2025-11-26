import Lemma.List.TakeAppend.eq.AppendTakeS
open List


@[main]
private lemma main
  {l₁ : List α}
-- given
  (h : n ≥ l₁.length)
  (l₂ : List α) :
-- imply
  (l₁ ++ l₂).take n = l₁ ++ l₂.take (n - l₁.length) := by
-- proof
  simpa [TakeAppend.eq.AppendTakeS]


-- created on 2025-11-03
