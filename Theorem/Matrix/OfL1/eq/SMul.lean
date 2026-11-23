module

public import Initialize.Tactic.Attr.Basic
public import Instance.Probability.Process.StochasticProcessTypes.Part3

public section


@[path]
public theorem main
  {S : Type*} [Fintype S]
-- given
  (c : ℝ) (x : S → ℝ) :
-- imply
  ofL1 (c • x) = c • ofL1 x := by
-- proof
  ext
  simp [ofL1]


-- created on 2026-09-22
