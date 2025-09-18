import Lemma.Basic


@[main]
private lemma main
  {n : ℕ}
-- given
  (h : n = n - 1) :
-- imply
  n = 0 := by
-- proof
  cases n <;>
    simp_all


-- created on 2025-06-21
