import sympy.stats.stochastic_process_types
import sympy.stats.stochastic_process
open scoped Matrix


@[main]
private lemma main
  [Fintype S]
  {P : Matrix S S ℝ} [RowStochastic P]
-- given
  (μ : Simplex S) :
-- imply
  (smat_as_operator P μ : l1Space S) = WithLp.toLp 1 ((WithLp.ofLp (μ : l1Space S)) ᵥ* P) :=
-- proof
  rfl

-- created on 2026-09-22
