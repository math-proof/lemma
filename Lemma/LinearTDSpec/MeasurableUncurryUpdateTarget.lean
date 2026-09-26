import sympy.stats.linear_td
import sympy.Basic
import Lemma.LinearTDSpec.MeasurableUncurryUpdate


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {d : ℕ}
  {spec : LinearTDSpec S d} :
-- imply
  Measurable (Function.uncurry spec.update_target) :=
-- proof
  LinearTDSpec.MeasurableUncurryUpdate.add measurable_fst


-- created on 2026-09-26
