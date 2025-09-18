import stdlib.Slice
import Lemma.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.tail = []) :
-- imply
  s.length ≤ 1 := by
-- proof
  cases s <;> simp_all


-- created on 2025-05-05
