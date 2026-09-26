import sympy.Basic
import sympy.stats.stochastic_process_types
open WithLp


@[main]
private lemma main
  {S : Type*} [Fintype S]
-- given
  (f : l1Space S) :
-- imply
  ‖f‖ = ∑ s, |f.ofLp s| := by
-- proof
  simpa using (PiLp.norm_eq_sum (f := f))

-- created on 2026-09-19
