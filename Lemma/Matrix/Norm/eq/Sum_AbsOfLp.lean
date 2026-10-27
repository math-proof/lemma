import Initialize.Tactic.Attr.Basic
import Instance.Probability.Process.StochasticProcessTypes.Part3
open WithLp


@[path]
private lemma main
  {S : Type*} [Fintype S]
-- given
  (f : l1Space S) :
-- imply
  ‖f‖ = ∑ s, |f.ofLp s| := by
-- proof
  simpa using (PiLp.norm_eq_sum (f := f))

-- created on 2026-09-19
