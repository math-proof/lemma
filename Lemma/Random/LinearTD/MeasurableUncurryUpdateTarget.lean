import Lemma.Random.LinearTD.MeasurableUncurryUpdate
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {d : ℕ}
  {spec : LinearTDSpec S d} :
-- imply
  Measurable (Function.uncurry spec.update_target) :=
-- proof
  Random.LinearTD.MeasurableUncurryUpdate.add measurable_fst


-- created on 2026-09-26
-- updated on 2026-11-17
