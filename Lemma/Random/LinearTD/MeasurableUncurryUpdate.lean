import sympy.stats.linear_td
import sympy.Basic


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {d : ℕ}
  {spec : LinearTDSpec S d} :
-- imply
  Measurable (Function.uncurry spec.update) :=
-- proof
  measurable_from_prod_countable_left fun y => Continuous.measurable (by simp only [Function.uncurry_apply_pair, LinearTDSpec.update]; fun_prop)


-- created on 2026-09-26
