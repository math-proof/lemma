import Lemma.Random.MeasurableUncurryUpdate
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {S A : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A]
  {spec : QLearningSpec S A} :
-- imply
  Measurable (Function.uncurry spec.update_target) :=
-- proof
  Random.MeasurableUncurryUpdate.add measurable_fst


-- created on 2026-09-26
-- updated on 2026-11-17
