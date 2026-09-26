import sympy.stats.q_learning
import sympy.Basic
import Lemma.QLearningSpec.MeasurableUncurryUpdate


@[main]
private lemma main
  {S A : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A]
  {spec : QLearningSpec S A} :
-- imply
  Measurable (Function.uncurry spec.update_target) :=
-- proof
  QLearningSpec.MeasurableUncurryUpdate.add measurable_fst


-- created on 2026-09-26
