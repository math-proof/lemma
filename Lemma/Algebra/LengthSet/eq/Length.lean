import Lemma.Basic


@[main]
private lemma main
  -- given
  (x : List α)
  (d : ℕ)
  (a : α) :
-- imply
  (x.set d a).length = x.length := by
-- proof
  simp


-- created on 2025-07-05
