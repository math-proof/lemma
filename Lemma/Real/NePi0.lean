import Lemma.Real.GtPi0
open Real


@[main]
private lemma main :
-- imply
  π ≠ 0 := by
-- proof
  linarith [GtPi0]


-- created on 2025-03-02
-- updated on 2026-08-03
