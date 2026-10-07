import sympy.stats.markov_reward_process
import sympy.Basic
import Lemma.Matrix.All_Gt_0.of.Stationary.StochasticIrreducible
open Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {MRP : FiniteMRP S} :
-- imply
  MRP.D.PosDef := by
-- proof
  exact PosDef.diagonal (All_Gt_0.of.Stationary.StochasticIrreducible (μ := MRP.μ) (P := MRP.P) inferInstance inferInstance)


-- created on 2026-09-26