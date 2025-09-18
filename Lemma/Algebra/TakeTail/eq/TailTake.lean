import Lemma.Basic


@[main, comm]
private lemma main
-- given
  (a : List α)
  (i : ℕ):
-- imply
  a.tail.take i = (a.take (i + 1)).tail := by
-- proof
  cases a <;>
    cases i <;>
      simp [List.take, List.tail]


-- created on 2025-06-17
-- updated on 2025-07-06
