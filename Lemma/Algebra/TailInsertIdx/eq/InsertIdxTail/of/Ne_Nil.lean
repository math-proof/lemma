import Lemma.Basic


@[main]
private lemma main
  {v : List α}
-- given
  (h : v ≠ [])
  (n : ℕ)
  (x : α) :
-- imply
  (v.insertIdx (n + 1) x).tail = v.tail.insertIdx n x := by
-- proof
  cases v <;>
    simp_all


-- created on 2025-07-13
