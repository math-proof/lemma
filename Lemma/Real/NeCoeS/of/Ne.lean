import Lemma.Real.EqCoeS.is.Eq
open Real


@[main]
private lemma main
  {a b : ℝ}
-- given
  (h : a ≠ b) :
-- imply
  (a : ℝ*) ≠ (b : ℝ*) := by
-- proof
  contrapose! h
  rwa [EqCoeS.is.Eq] at h


-- created on 2025-12-10
